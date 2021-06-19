use std::collections::HashMap;

use lir::GetLocals;

use crate::lir;

use super::Optimize;

pub(super) struct BranchElim();

impl Optimize for BranchElim {
    fn level(&self) -> usize {
        0
    }

    fn optimize_func(&self, func: &mut lir::Func) {
        fn optimize_inst<'a, I>(it: I, _: &mut HashMap<usize, usize>)
        where
            I: IntoIterator<Item = &'a mut lir::Inst>,
        {
            for inst in it {
                match inst {
                    lir::Inst::Call(_)
                    | lir::Inst::CExternCall(_)
                    | lir::Inst::Free(_)
                    | lir::Inst::SetGlobal(_, _)
                    | lir::Inst::SetLocal(_, _)
                    | lir::Inst::Store(_)
                    | lir::Inst::MemCopy(_, _, _)
                    | lir::Inst::IncRef(_, _)
                    | lir::Inst::DecRef(_)
                    | lir::Inst::Return(_)
                    | lir::Inst::If(_)
                    | lir::Inst::Break(_)
                    | lir::Inst::Goto(_)
                    | lir::Inst::Halt => todo!(),
                }
            }
        }

        let mut use_map = func.count_local_uses();
        optimize_inst(func, &mut use_map)
    }
}
