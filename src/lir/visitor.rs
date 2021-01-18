use std::collections::VecDeque;

use crate::lir;

pub struct InstIter<'a> {
    inst: VecDeque<&'a lir::Inst>,
}

impl<'a> Iterator for InstIter<'a> {
    type Item = &'a lir::Inst;

    fn next(&mut self) -> Option<&'a lir::Inst> {
        let inst = self.inst.pop_front();
        if let Some(inst) = inst {
            match &inst.kind {
                lir::InstKind::Block(b) => {
                    self.inst.extend(b.instructions.iter());
                }
                lir::InstKind::Func(f) => {
                    self.inst.extend(f.body.instructions.iter());
                }
                lir::InstKind::IfBlock(b) => {
                    self.inst.extend(
                        b.cond
                            .instructions
                            .iter()
                            .chain(b.then.instructions.iter())
                            .chain(b.els.instructions.iter()),
                    );
                }
                lir::InstKind::Loop(l) => {
                    self.inst.extend(
                        l.begin
                            .instructions
                            .iter()
                            .chain(l.cond.instructions.iter())
                            .chain(l.body.instructions.iter())
                            .chain(l.end.instructions.iter()),
                    );
                }
                _ => (),
            }
        }

        inst
    }
}

impl<'a> From<&'a lir::Func> for InstIter<'a> {
    fn from(f: &'a lir::Func) -> Self {
        InstIter {
            inst: f.body.instructions.iter().collect(),
        }
    }
}
