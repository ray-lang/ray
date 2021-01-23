use std::{cell::RefMut, collections::VecDeque};

use crate::{
    ast::{Node, SourceInfo},
    lir,
};

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

// impl<'a> IntoIterator for &'a lir::Func {
//     type Item = &'a lir::Inst;

//     type IntoIter = std::vec::IntoIter<&'a lir::Inst>;

//     fn into_iter(self) -> Self::IntoIter {
//         fn append<'a>(inst: &'a lir::Inst, v: &mut Vec<&'a lir::Inst>) {
//             match &inst {
//                 lir::Inst::Block(b) => {
//                     for i in b.instructions.iter() {
//                         append(i, v);
//                     }
//                     return;
//                 }
//                 lir::Inst::Func(f) => {
//                     for i in f.body.instructions.iter() {
//                         append(i, v);
//                     }
//                     return;
//                 }
//                 lir::Inst::IfBlock(b) => {
//                     for i in b
//                         .cond
//                         .instructions
//                         .iter()
//                         .chain(b.then.instructions.iter())
//                         .chain(b.els.instructions.iter())
//                     {
//                         append(i, v);
//                     }
//                     return;
//                 }
//                 lir::Inst::Loop(l) => {
//                     for i in l
//                         .begin
//                         .instructions
//                         .iter()
//                         .chain(l.cond.instructions.iter())
//                         .chain(l.body.instructions.iter())
//                         .chain(l.end.instructions.iter())
//                     {
//                         append(i, v);
//                     }
//                     return;
//                 }
//                 _ => (),
//             }

//             v.push(inst);
//         }

//         let mut result = vec![];
//         for inst in self.body.instructions.iter() {
//             append(inst, &mut result);
//         }
//         result.into_iter()
//     }
// }

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

// pub struct InstIter<'a> {
//     inst: VecDeque<&'a lir::Inst>,
// }

// pub struct InstIterMut<'a> {
//     inst: VecDeque<&'a mut Node<lir::Inst, SourceInfo>>,
// }

// impl<'a> Iterator for InstIter<'a> {
//     type Item = &'a lir::Inst;

//     fn next(&mut self) -> Option<&'a lir::Inst> {
//         let inst = self.inst.pop_front();
//         if let Some(inst) = inst {
//             match &inst.kind {
//                 lir::InstKind::Block(b) => {
//                     self.inst.extend(b.instructions.iter());
//                 }
//                 lir::InstKind::Func(f) => {
//                     self.inst.extend(f.body.instructions.iter());
//                 }
//                 lir::InstKind::IfBlock(b) => {
//                     self.inst.extend(
//                         b.cond
//                             .instructions
//                             .iter()
//                             .chain(b.then.instructions.iter())
//                             .chain(b.els.instructions.iter()),
//                     );
//                 }
//                 lir::InstKind::Loop(l) => {
//                     self.inst.extend(
//                         l.begin
//                             .instructions
//                             .iter()
//                             .chain(l.cond.instructions.iter())
//                             .chain(l.body.instructions.iter())
//                             .chain(l.end.instructions.iter()),
//                     );
//                 }
//                 _ => (),
//             }
//         }

//         inst
//     }
// }

// impl<'a> From<&'a lir::Func> for InstIter<'a> {
//     fn from(f: &'a lir::Func) -> Self {
//         InstIter {
//             inst: f.body.instructions.iter().collect(),
//         }
//     }
// }

// impl<'a> Iterator for InstIterMut<'a> {
//     type Item = &'a mut Node<lir::Inst, SourceInfo>;

//     fn next(&mut self) -> Option<&'a mut Node<lir::Inst, SourceInfo>> {
//         let inst = self.inst.pop_front();

//         inst
//     }
// }

// impl<'a> From<VecDeque<&'a mut Node<lir::Inst, SourceInfo>>> for InstIterMut<'a> {
//     fn from(inst: VecDeque<&'a mut Node<lir::Inst, SourceInfo>>) -> Self {
//         InstIterMut { inst }
//     }
// }

// impl<'a> From<&'a mut lir::Func> for InstIterMut<'a> {
//     fn from(f: &'a mut lir::Func) -> Self {
//         InstIterMut {
//             inst: f.body.instructions.iter_mut().collect(),
//         }
//     }
// }
