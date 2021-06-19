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
        if let lir::Value::Atom(lir::Atom::Variable(lir::Variable::Local(rhs))) = val {
            // if the LHS and RHS are not the same local
            if lhs != *rhs {
                // if LHS and RHS are _not_ parameters
                if lhs >= params && *rhs >= params {
                    // replace all instances of LHS local with RHS
                    Some((lhs, *rhs))
                } else {
                    // LHS is a parameter
                    if *rhs < params {
                        // RHS is a parameter too; do nothing
                        return None;
                    }

                    // replace RHS with LHS instead (if RHS is not ALSO a parameter)
                    Some((*rhs, lhs))
                }
            } else {
                Some((lhs, *rhs))
            }
        } else {
            None
        }
    }

    // fn visit_block(
    //     &self,
    //     insts: &mut Vec<lir::Inst>,
    //     params: usize,
    //     local_map: &mut HashMap<usize, usize>,
    // ) {
    //     let iter = insts.drain(..).collect::<Vec<_>>();
    //     for mut inst in iter {
    //         if match &mut inst {
    //             lir::Inst::SetLocal(lhs, val) => self.visit_set_local(lhs, val, params, local_map),
    //             _ => true,
    //         } {
    //             insts.push(inst);
    //         }
    //     }
    // }
}
