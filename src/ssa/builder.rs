use std::collections::{HashMap, HashSet};

use crate::{ast::Node, graph::Graph, typing::ty::Ty};

use super::{Block, Callable, Expr, Local, Op, Value};

pub struct Vars {
    map: HashMap<String, (usize, usize)>,
}

pub struct SSABuilder {
    curr_block: usize,
    params: Vec<(String, Ty)>,
    locals: Vec<Local>,
    vars: HashMap<String, usize>,
    entry_block: Option<usize>,
    exit_block: Option<usize>,
    blocks: Vec<Block>,
    data: Vec<Vec<u8>>,
    cfg: Graph<usize, HashSet<usize>>,
}

impl SSABuilder {
    pub fn new() -> SSABuilder {
        SSABuilder {
            curr_block: 0,
            params: vec![],
            locals: vec![],
            vars: HashMap::new(),
            entry_block: None,
            exit_block: None,
            blocks: vec![],
            data: vec![],
            cfg: Graph::new(),
        }
    }

    pub fn done(
        mut self,
    ) -> (
        Vec<(String, Ty)>,
        Vec<Local>,
        Vec<Block>,
        Vec<Vec<u8>>,
        Graph<usize, HashSet<usize>>,
    ) {
        // ensure that each block has a final control flow instruction
        let num_blocks = self.blocks.len();
        let mut new_edges = vec![];
        for (idx, block) in self.blocks.iter_mut().enumerate() {
            if matches!(block.last(), Some(node)  if node.is_control()) {
                continue;
            }

            // add a goto to the next block
            if idx + 1 < num_blocks {
                block.push(Node::new(Expr::Goto(Node::new(idx + 1))));
                new_edges.push((idx, idx + 1));
            }
        }

        for (prec, succ) in new_edges {
            self.cfg.add_edge(prec, succ, None);
        }

        (self.params, self.locals, self.blocks, self.data, self.cfg)
    }

    pub fn local(&mut self, ty: Ty) -> usize {
        let idx = self.locals.len();
        let loc = Local { idx, ty };
        if self.blocks.len() != 0 {
            self.block().def_var(idx);
        }
        self.locals.push(loc);
        idx
    }

    pub fn var(&mut self, name: String, ty: Ty) -> usize {
        let idx = self.local(ty);
        self.vars.insert(name, idx);
        idx
    }

    #[inline(always)]
    pub fn set_var_loc(&mut self, name: String, loc: usize) {
        self.vars.insert(name, loc);
    }

    #[inline(always)]
    pub fn get_var_loc(&mut self, name: &String) -> Option<usize> {
        self.vars.get(name).copied()
    }

    pub fn get_var(&mut self, name: &String) -> Option<usize> {
        if let Some(loc) = self.vars.get(name).copied() {
            self.block().use_var(loc);
            Some(loc)
        } else {
            None
        }
    }

    pub fn param(&mut self, name: String, ty: Ty) -> usize {
        let idx = self.local(ty.clone());
        self.params.push((name.clone(), ty));
        self.vars.insert(name, idx);
        idx
    }

    #[inline(always)]
    pub fn block(&mut self) -> &mut Block {
        &mut self.blocks[self.curr_block]
    }

    pub fn new_block(&mut self) -> usize {
        let label = self.blocks.len();
        self.blocks.push(Block::new(label));
        label
    }

    pub fn add_entry_block(&mut self) -> usize {
        let idx = self.new_block();
        self.entry_block = Some(idx);
        idx
    }

    pub fn use_block(&mut self, label: usize) -> usize {
        let prev = self.curr_block;
        self.curr_block = label;
        prev
    }

    pub fn with_new_block<F, T>(&mut self, f: F) -> (usize, T)
    where
        F: FnOnce(&mut SSABuilder) -> T,
    {
        // to prevent nested blocks, don't create a new block if the current is empty
        let (label, prev_block) = if self.blocks.len() != 0 && self.block().is_empty() {
            (self.curr_block, self.curr_block)
        } else {
            let label = self.new_block();
            (label, self.curr_block)
        };

        self.curr_block = label;
        let t = f(self);
        self.curr_block = prev_block;
        (label, t)
    }

    pub fn with_block<F>(&mut self, label: usize, f: F)
    where
        F: FnOnce(&mut SSABuilder),
    {
        let prev_block = self.curr_block;
        self.curr_block = label;
        f(self);
        self.curr_block = prev_block;
    }

    pub fn with_entry_block<F>(&mut self, f: F)
    where
        F: FnOnce(&mut SSABuilder),
    {
        let entry_label = if let Some(label) = self.entry_block {
            label
        } else {
            let label = self.new_block();
            self.entry_block = Some(label);
            label
        };

        let prev_block = self.curr_block;
        self.curr_block = entry_label;
        f(self);
        self.curr_block = prev_block;
    }

    pub fn with_exit_block<F>(&mut self, f: F)
    where
        F: FnOnce(&mut SSABuilder),
    {
        let exit_block = if let Some(label) = self.exit_block {
            label
        } else {
            let label = self.new_block();
            self.exit_block = Some(label);
            label
        };

        let prev_block = self.curr_block;
        self.curr_block = exit_block;
        f(self);
        self.curr_block = prev_block;
    }

    pub fn data(&mut self, bytes: Vec<u8>) -> usize {
        let idx = self.data.len();
        self.data.push(bytes);
        idx
    }

    pub fn cfg(&mut self) -> &mut Graph<usize, HashSet<usize>> {
        &mut self.cfg
    }

    pub fn push(&mut self, value: Node<Expr>) {
        self.block().push(value)
    }

    pub fn store(&mut self, dst: usize, src: Value, size: Value, offset: Value) {
        let loc = Node::new(self.local(Ty::Never));
        self.block().push(Node::new(Expr::Set(
            loc,
            Node::new(Value::Call(
                Node::new(Callable::Op(Op::Store)),
                vec![
                    Node::new(Value::Local(dst)),
                    Node::new(src),
                    Node::new(size),
                    Node::new(offset),
                ],
            )),
        )));
    }

    pub fn set(&mut self, lhs: Node<usize>, rhs: Node<Value>) {
        self.block().push(Node::new(Expr::Set(lhs, rhs)));
    }

    pub fn phi(&mut self, lhs: Node<usize>, labels: Vec<(usize, Node<usize>)>) {
        self.block().push(Node::new(Expr::Phi(lhs, labels)));
    }

    pub fn goto(&mut self, label: usize) {
        self.cfg.add_edge(self.curr_block, label, None);
        self.block().push(Node::new(Expr::Goto(Node::new(label))))
    }

    pub fn ret(&mut self, loc: Node<usize>) {
        self.block().use_var(*loc);
        self.block()
            .push(Node::new(Expr::Ret(loc.take_map(|loc| Value::Local(loc)))));
    }

    pub fn cond_branch(&mut self, cond_loc: Node<usize>, then_label: usize, else_label: usize) {
        self.cfg.add_edge(self.curr_block, then_label, None);
        self.cfg.add_edge(self.curr_block, else_label, None);
        self.push(Node::new(Expr::If(
            cond_loc,
            Node::new(then_label),
            Node::new(else_label),
        )));
    }
}
