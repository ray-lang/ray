use std::collections::HashSet;

use lir::MapLocals;

use crate::lir;

use super::{reindex_locals, Optimize};

pub(super) struct SimplifyPhiNodes();

impl Optimize for SimplifyPhiNodes {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, func: &mut lir::Func) {
        let params = func.params.len();
        let mut replaced = HashSet::new();
        let mut idx = 0;
        while idx < func.blocks.len() {
            let mut inst_idx = 0;
            let body_size = func.blocks[idx].len();
            while inst_idx < body_size {
                let (lhs, values) = if let lir::Inst::SetLocal(lhs, lir::Value::Phi(phi)) =
                    &mut func.blocks[idx][inst_idx]
                {
                    (*lhs, phi.values().clone())
                } else {
                    inst_idx += 1;
                    continue;
                };

                let new_loc = if lhs >= params && values.iter().all(|(_, loc)| lhs <= *loc) {
                    lhs
                } else {
                    values.iter().map(|&(_, loc)| loc).min().unwrap()
                };

                for (_, loc) in values {
                    if loc != new_loc && loc >= params {
                        func.replace_local(loc, new_loc);
                        log::debug!("replaced {} with {}: {}", loc, new_loc, func);
                        replaced.insert(loc);
                    }
                }

                if lhs != new_loc && lhs >= params {
                    func.replace_local(lhs, new_loc);
                    log::debug!("replaced {} with {}: {}", lhs, new_loc, func);
                    replaced.insert(lhs);
                }

                let var = lir::Variable::Local(new_loc);
                if let lir::Inst::SetLocal(_, val) = &mut func.blocks[idx][inst_idx] {
                    *val = lir::Atom::Variable(var).into()
                }

                inst_idx += 1;
            }

            idx += 1;
        }

        // reindex
        reindex_locals(func, &replaced);
        log::debug!("simplify phi: {}", func);
    }
}
