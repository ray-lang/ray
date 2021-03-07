use std::collections::HashMap;

use crate::lir::{self, MapLocals};

use super::Optimize;

pub(super) struct RedundantAssignElim();

impl Optimize for RedundantAssignElim {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, func: &mut lir::Func) {
        let params = func.params.len();
        let mut local_map = HashMap::new();
        self.visit_block(&mut func.body, params, &mut local_map);
        self.reindex_locals(func, &local_map);
    }
}

impl RedundantAssignElim {
    fn reindex_locals(&self, func: &mut lir::Func, local_map: &HashMap<usize, usize>) {
        // first map the replaced locals
        func.map_locals(local_map);

        // determine the locals that were _not_ replaced
        let locals = func.locals.drain(..).collect::<Vec<_>>();
        let mut reindex = HashMap::new();
        for (i, loc) in locals.into_iter().enumerate() {
            if !local_map.contains_key(&i) {
                let new_idx = func.locals.len();
                func.locals.push(loc);
                reindex.insert(i, new_idx);
            }
        }

        // then reindex the locals
        func.map_locals(&reindex);
    }

    fn visit_set_local(
        &self,
        lhs: &usize,
        val: &lir::Value,
        params: usize,
        local_map: &mut HashMap<usize, usize>,
    ) -> bool {
        // if RHS is a local, then this instruction is unecessary
        if let lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(rhs))) = val {
            // if the LHS and RHS are not the same local
            if lhs != rhs {
                // if LHS is _not_ a parameter
                if *lhs >= params {
                    // check if RHS is _also_ being replaced
                    if let Some(&loc) = local_map.get(rhs) {
                        // use this one instead
                        local_map.insert(*lhs, loc);
                    } else {
                        // replace all instances of LHS local with RHS
                        local_map.insert(*lhs, *rhs);
                    }
                } else {
                    // LHS is a parameter
                    if *rhs < params {
                        // RHS is a parameter too; do nothing
                        return true;
                    }

                    // replace RHS with LHS instead (if RHS is not ALSO a parameter)
                    local_map.insert(*rhs, *lhs);
                }
            }

            false
        } else {
            true
        }
    }

    fn visit_block(
        &self,
        block: &mut lir::Block,
        params: usize,
        local_map: &mut HashMap<usize, usize>,
    ) {
        let insts = block.instructions.drain(..).collect::<Vec<_>>();
        for mut i in insts {
            if self.visit_inst(&mut i, params, local_map) {
                block.instructions.push(i);
            }
        }
    }

    fn visit_inst(
        &self,
        inst: &mut lir::Inst,
        params: usize,
        local_map: &mut HashMap<usize, usize>,
    ) -> bool {
        match inst {
            lir::Inst::SetLocal(loc, val) => self.visit_set_local(loc, val, params, local_map),
            lir::Inst::Block(block) => {
                self.visit_block(block, params, local_map);
                true
            }
            lir::Inst::IfBlock(b) => {
                self.visit_block(&mut b.cond_block, params, local_map);
                self.visit_block(&mut b.then_block, params, local_map);
                self.visit_block(&mut b.else_block, params, local_map);
                true
            }
            lir::Inst::Loop(l) => {
                self.visit_block(&mut l.begin, params, local_map);
                self.visit_block(&mut l.cond, params, local_map);
                self.visit_block(&mut l.body, params, local_map);
                self.visit_block(&mut l.end, params, local_map);
                true
            }
            _ => true,
        }
    }
}
