use crate::{
    ast::{Node, SourceInfo},
    lir,
};

pub trait IterCalls<'a> {
    fn iter_calls(self) -> std::vec::IntoIter<&'a mut Node<lir::Inst, SourceInfo>>;
}

impl<'a, I> IterCalls<'a> for I
where
    I: IntoIterator<Item = &'a mut Node<lir::Inst, SourceInfo>>,
{
    fn iter_calls(self) -> std::vec::IntoIter<&'a mut Node<lir::Inst, SourceInfo>> {
        let mut calls = vec![];
        for inst in self {
            let inst = match &inst.value {
                lir::Inst::Value(v)
                | lir::Inst::SetGlobal(_, v)
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
                _ => continue,
            };

            calls.push(inst);
        }

        calls.into_iter()
    }
}

impl<'a> IntoIterator for &'a mut lir::Program {
    type Item = &'a mut Node<lir::Inst, SourceInfo>;

    type IntoIter = std::vec::IntoIter<&'a mut Node<lir::Inst, SourceInfo>>;

    fn into_iter(self) -> Self::IntoIter {
        let mut result = vec![];
        for func in self.funcs.iter_mut() {
            result.extend(func.into_iter());
        }
        result.into_iter()
    }
}

impl<'a> IntoIterator for &'a mut lir::Func {
    type Item = &'a mut Node<lir::Inst, SourceInfo>;

    type IntoIter = std::vec::IntoIter<&'a mut Node<lir::Inst, SourceInfo>>;

    fn into_iter(self) -> Self::IntoIter {
        fn append<'a>(
            inst: &'a mut Node<lir::Inst, SourceInfo>,
            v: &mut Vec<&'a mut Node<lir::Inst, SourceInfo>>,
        ) {
            if matches!(&inst.value, lir::Inst::Block(_)) {
                if let lir::Inst::Block(b) = &mut inst.value {
                    for i in b.instructions.iter_mut() {
                        append(i, v);
                    }
                }
            } else if matches!(&inst.value, lir::Inst::Func(_)) {
                if let lir::Inst::Func(f) = &mut inst.value {
                    for i in f.body.instructions.iter_mut() {
                        append(i, v);
                    }
                }
            } else if matches!(&inst.value, lir::Inst::IfBlock(_)) {
                if let lir::Inst::IfBlock(b) = &mut inst.value {
                    for i in b
                        .cond
                        .instructions
                        .iter_mut()
                        .chain(b.then.instructions.iter_mut())
                        .chain(b.els.instructions.iter_mut())
                    {
                        append(i, v);
                    }
                }
            } else if matches!(&inst.value, lir::Inst::Loop(_)) {
                if let lir::Inst::Loop(l) = &mut inst.value {
                    for i in l
                        .begin
                        .instructions
                        .iter_mut()
                        .chain(l.cond.instructions.iter_mut())
                        .chain(l.body.instructions.iter_mut())
                        .chain(l.end.instructions.iter_mut())
                    {
                        append(i, v);
                    }
                }
            } else {
                v.push(inst);
            }
        }

        let mut result = vec![];
        for inst in self.body.instructions.iter_mut() {
            append(inst, &mut result);
        }
        result.into_iter()
    }
}
