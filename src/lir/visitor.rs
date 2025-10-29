use crate::lir;

pub trait IterCalls<'a> {
    fn iter_calls(self) -> std::vec::IntoIter<&'a mut lir::Inst>;
}

impl<'a, I> IterCalls<'a> for I
where
    I: IntoIterator<Item = &'a mut lir::Inst>,
{
    fn iter_calls(self) -> std::vec::IntoIter<&'a mut lir::Inst> {
        let mut calls = vec![];
        for inst in self {
            let inst = match inst {
                lir::Inst::SetGlobal(_, v)
                | lir::Inst::SetLocal(_, v)
                | lir::Inst::IncRef(v, _)
                | lir::Inst::DecRef(v)
                | lir::Inst::Return(v) => {
                    if matches!(v, lir::Value::Call(_)) {
                        inst
                    } else {
                        continue;
                    }
                }
                lir::Inst::Store(s) => {
                    if matches!(s.value, lir::Value::Call(_)) {
                        inst
                    } else {
                        continue;
                    }
                }
                lir::Inst::SetField(s) => {
                    if matches!(s.value, lir::Value::Call(_)) {
                        inst
                    } else {
                        continue;
                    }
                }
                lir::Inst::Call(_) => inst,

                lir::Inst::CExternCall(_) => todo!(),

                lir::Inst::Free(_)
                | lir::Inst::MemCopy(_, _, _)
                | lir::Inst::If(_)
                | lir::Inst::StructInit(_, _)
                | lir::Inst::Break(_)
                | lir::Inst::Goto(_) => continue,
            };

            calls.push(inst);
        }

        calls.into_iter()
    }
}

impl<'a> IntoIterator for &'a mut lir::Program {
    type Item = &'a mut lir::Inst;

    type IntoIter = std::vec::IntoIter<&'a mut lir::Inst>;

    fn into_iter(self) -> Self::IntoIter {
        let mut result = vec![];
        for func in self.funcs.iter_mut() {
            result.extend(func.into_iter());
        }
        result.into_iter()
    }
}

impl<'a> IntoIterator for &'a mut lir::Func {
    type Item = &'a mut lir::Inst;

    type IntoIter = std::vec::IntoIter<&'a mut lir::Inst>;

    fn into_iter(self) -> Self::IntoIter {
        let mut result = vec![];
        for block in self.blocks.iter_mut() {
            for inst in block.iter_mut() {
                result.push(inst);
            }
        }
        result.into_iter()
    }
}
