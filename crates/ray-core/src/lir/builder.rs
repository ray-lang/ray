use std::collections::HashMap;

use ray_typing::ty::{Ty, TyScheme};

use super::{Block, ControlFlowGraph, If, Inst, Local, Param, SymbolSet, Value};

pub type VarMap = HashMap<String, usize>;

#[derive(Clone, Debug)]
pub struct Builder {
    pub(super) curr_block: usize,
    pub(super) control_block: Option<usize>,
    pub(super) params: Vec<Param>,
    pub(super) locals: Vec<Local>,
    pub(super) vars: VarMap,
    pub(super) entry_block: Option<usize>,
    pub(super) exit_block: Option<usize>,
    pub(super) blocks: Vec<Block>,
    pub(super) symbols: SymbolSet,
    pub(super) cfg: ControlFlowGraph,
}

impl Builder {
    pub fn new() -> Builder {
        Builder {
            curr_block: 0,
            control_block: None,
            params: vec![],
            locals: vec![],
            vars: HashMap::new(),
            entry_block: None,
            exit_block: None,
            blocks: vec![],
            symbols: SymbolSet::new(),
            cfg: ControlFlowGraph::default(),
        }
    }

    pub fn done(
        mut self,
    ) -> (
        Vec<Param>,
        Vec<Local>,
        Vec<Block>,
        SymbolSet,
        ControlFlowGraph,
    ) {
        // ensure that each block has a final control flow instruction
        let num_blocks = self.blocks.len();
        let mut new_edges = vec![];
        for (idx, block) in self.blocks.iter_mut().enumerate() {
            if matches!(block.last(), Some(inst) if inst.is_control()) {
                continue;
            }

            // add a goto to the next block
            if idx + 1 < num_blocks {
                block.push(Inst::Goto(idx + 1));
                new_edges.push((idx, idx + 1));
            }
        }

        self.cfg.extend_with_edges(new_edges);

        (
            self.params,
            self.locals,
            self.blocks,
            self.symbols,
            self.cfg,
        )
    }

    pub fn local(&mut self, ty: TyScheme) -> usize {
        let idx = self.locals.len();
        let loc = Local { idx, ty };
        self.locals.push(loc);
        idx
    }

    #[inline(always)]
    pub fn get_var(&self, name: &String) -> Option<&usize> {
        self.vars.get(name)
    }

    #[inline(always)]
    pub fn set_var(&mut self, name: String, idx: usize) {
        self.block().define_var(name.clone(), idx);
        self.vars.insert(name, idx);
    }

    pub fn param(&mut self, name: String, ty: Ty) -> usize {
        let idx = self.local(ty.clone().into());
        self.params.push(Param::new(name.clone(), idx, ty));
        self.set_var(name, idx);
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

    #[allow(dead_code)]
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

    pub fn push(&mut self, value: Inst) {
        self.block().push(value)
    }

    pub fn goto(&mut self, label: usize) -> Option<usize> {
        if label == self.block().label() {
            return None;
        }

        if let Some(inst) = self.block().last() {
            match inst {
                &Inst::Goto(label) => return Some(label),
                Inst::If(_) | Inst::Return(_) => return None,
                _ => {}
            }
        }

        self.branch(label);
        self.block().push(Inst::Goto(label));
        None
    }

    pub fn branch(&mut self, label: usize) {
        let prec = self.block().label();
        self.cfg.extend_with_edges(&[(prec, label)]);
    }

    pub fn ret(&mut self, value: Value) {
        self.block().push(Inst::Return(value))
    }

    pub fn cond(&mut self, cond_loc: usize, then_label: usize, else_label: usize) {
        self.branch(then_label);
        self.branch(else_label);
        self.push(If::new(cond_loc, then_label, else_label).into());
    }
}
