use std::collections::HashSet;

use lir::MapLocals;

use crate::lir;

use super::{reindex_locals, Optimize};

pub(super) struct RedundantAssignElim();

impl Optimize for RedundantAssignElim {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, func: &mut lir::Func) {
        let params = func.params.len();
        let mut replaced = HashSet::new();
        let mut idx = 0;
        while idx < func.blocks.len() {
            let mut inst_idx = 0;
            while inst_idx < func.blocks[idx].len() {
                let inst = &mut func.blocks[idx][inst_idx];
                if let lir::Inst::SetLocal(lhs, val) = inst {
                    if let Some((old, new)) = self.visit_set_local(*lhs, val, params) {
                        if old != new {
                            func.replace_local(old, new);
                            replaced.insert(old);
                        }

                        // remove this instruction
                        func.blocks[idx].remove(inst_idx);
                        continue;
                    }
                }

                inst_idx += 1;
            }

            idx += 1;
        }

        reindex_locals(func, &replaced);
        log::debug!("assign elim: {}", func);
    }
}

impl RedundantAssignElim {
    fn visit_set_local(
        &self,
        lhs: usize,
        val: &lir::Value,
        params: usize,
    ) -> Option<(usize, usize)> {
        // if RHS is a local, then this instruction is unecessary
        if let &lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(rhs))) = val {
            // if the LHS and RHS are not the same local
            if lhs != rhs {
                if rhs >= params {
                    // LHS is a parameter and RHS is not
                    // replace RHS with LHS instead
                    Some((rhs, lhs))
                } else if lhs >= params {
                    // if LHS is not a parameter and RHS is either
                    // replace all instances of LHS local with RHS
                    Some((lhs, rhs))
                } else {
                    // both are parameters; do nothing
                    None
                }
            } else {
                Some((lhs, rhs))
            }
        } else {
            None
        }
    }
}
