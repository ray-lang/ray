use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    ops::DerefMut,
    rc::Rc,
};

use crate::{
    ast::{Node, Path},
    lir::{self, Inst, Store, Value},
    span::SourceMap,
};

use super::Optimize;

pub(super) struct Inline();

impl Optimize for Inline {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, _: &mut lir::Func) {
        unreachable!("this should not be called")
    }

    fn optimize(&self, prog: &mut lir::Program, srcmap: &SourceMap) {
        // walk the program and find calls to inline
        let func_names = prog
            .funcs
            .iter()
            .map(|f| f.name.clone())
            .collect::<Vec<_>>();
        let mut funcs = prog
            .funcs
            .drain(..)
            .map(|f| (f.name.clone(), Rc::new(RefCell::new(f))))
            .collect::<HashMap<_, _>>();

        for f in funcs.values().cloned() {
            let mut locals = f.borrow().locals.clone();
            let mut fn_mut = f.borrow_mut();
            let mut removed_symbols = HashSet::new();
            self.iter_blocks(
                &mut fn_mut.blocks,
                &mut removed_symbols,
                &mut locals,
                &funcs,
                srcmap,
            );

            for f in removed_symbols {
                fn_mut.symbols.remove(&f);
            }
            fn_mut.locals = locals;
        }

        // insert in the same order
        for name in func_names {
            if let Some(f) = funcs.remove(&name) {
                prog.funcs.push(Rc::try_unwrap(f).unwrap().into_inner());
            }
        }
    }
}

impl Inline {
    fn inline_call(
        &self,
        inst: &mut Inst,
        fn_name: &Path,
        args: Vec<lir::Variable>,
        result_local: Option<lir::Variable>,
        locals: &mut Vec<lir::Local>,
        funcs: &HashMap<Path, Rc<RefCell<Node<lir::Func>>>>,
        srcmap: &SourceMap,
    ) -> Option<Vec<lir::Block>> {
        if let Some(f) = funcs.get(fn_name) {
            if srcmap.has_inline(&f.borrow()) {
                let f = f.borrow().clone();
                let (new_locs, new_blocks) = f.value.inline(args, result_local, locals.len());
                locals.extend(new_locs);
                Some(new_blocks)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn iter_insts(
        &self,
        block: &mut lir::Block,
        start_idx: usize,
        removed_symbols: &mut HashSet<Path>,
        locals: &mut Vec<lir::Local>,
        funcs: &HashMap<Path, Rc<RefCell<Node<lir::Func>>>>,
        srcmap: &SourceMap,
    ) -> Option<(lir::Block, usize)> {
        let mut idx = start_idx;
        while idx < block.len() {
            let inst = &mut block[idx];
            if let Some((local, fn_name, args)) = match inst {
                Inst::SetGlobal(loc, Value::Call(c)) => Some((
                    Some(lir::Variable::Global(*loc)),
                    c.fn_name.clone(),
                    c.args.clone(),
                )),
                Inst::SetLocal(loc, Value::Call(c)) => Some((
                    Some(lir::Variable::Local(*loc)),
                    c.fn_name.clone(),
                    c.args.clone(),
                )),
                Inst::Call(c)
                | Inst::IncRef(Value::Call(c), _)
                | Inst::DecRef(Value::Call(c))
                | Inst::Return(Value::Call(c))
                | Inst::Store(Store {
                    value: Value::Call(c),
                    ..
                }) => Some((None, c.fn_name.clone(), c.args.clone())),
                _ => None,
            } {
                if let Some(new_blocks) =
                    self.inline_call(inst, &fn_name, args, local, locals, funcs, srcmap)
                {
                    removed_symbols.insert(fn_name);
                    // split the block into two new blocks, one before the call and one after
                    let mut new_block = block.split_off(idx);

                    // remove _this_ instruction
                    new_block.pop();
                    return Some((new_block, idx));
                }
            }
            idx += 1;
        }

        None
    }

    fn iter_blocks(
        &self,
        blocks: &mut Vec<lir::Block>,
        removed_symbols: &mut HashSet<Path>,
        locals: &mut Vec<lir::Local>,
        funcs: &HashMap<Path, Rc<RefCell<Node<lir::Func>>>>,
        srcmap: &SourceMap,
    ) {
        let mut idx = 0;
        while idx < blocks.len() {
            let block = &mut blocks[idx];
            let mut new_blocks = vec![];
            let mut start_idx = 0;
            while let Some((new_block, new_idx)) =
                self.iter_insts(block, start_idx, removed_symbols, locals, funcs, srcmap)
            {
                new_blocks.push((idx + new_blocks.len() + 1, new_block));
                start_idx = new_idx;
            }

            for (idx, block) in new_blocks {
                blocks.insert(idx, block);
            }

            idx += 1;
        }
    }
}
