use std::collections::HashMap;

use crate::lir;

use super::Transform;

pub struct ToSSAForm();

impl Transform for ToSSAForm {
    type Ctx = HashMap<String, Vec<(usize, usize)>>;

    fn transform_func(&mut self, func: &mut lir::Func) {
        log::debug!("BEFORE to ssa: {}", func);
        let frontiers = func.calculate_dominators();

        let mut idx = 0;
        while idx < func.blocks.len() {
            let mut ctx: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
            if let Some(dominators) = frontiers.get(&idx) {
                log::debug!("{} is dominated by {:?}", idx, dominators);

                for &label in dominators {
                    let pred = &func.blocks[label];
                    for (var, &idx) in pred.defined_vars() {
                        ctx.entry(var.clone()).or_default().push((label, idx));
                    }
                }
            }

            let block = &mut func.blocks[idx];
            self.transform_block(block, &ctx);
            idx += 1;
        }

        log::debug!("to ssa: {}", func);
    }

    fn transform_block(&mut self, block: &mut lir::Block, ctx: &Self::Ctx) {
        let mut idx = 0;
        while idx < block.len() {
            let inst = &mut block[idx];
            let remove = if let lir::Inst::SetLocal(_, lir::Value::VarRef(var)) = inst {
                // this means that this is the first definition of the variable;
                // in this case, we don't need this assignmnet
                ctx.get(var).is_none()
            } else {
                false
            };

            if remove {
                block.remove(idx);
                continue;
            }

            self.transform_inst(inst, ctx);
            idx += 1;
        }
    }

    fn transform_inst(&mut self, inst: &mut lir::Inst, ctx: &Self::Ctx) {
        if let lir::Inst::SetLocal(_, val) = inst {
            if let lir::Value::VarRef(var) = &val {
                // lookup the variable in the map
                let var = var.clone();
                if let Some(values) = ctx.get(&var).cloned() {
                    if values.len() == 1 {
                        let (_, loc) = values[0];
                        *val = lir::Atom::Variable(lir::Variable::Local(loc)).into();
                    } else {
                        *val = lir::Phi::new(values).into();
                    }
                }
            }
        }
    }
}

pub fn to_ssa(prog: &mut lir::Program) {
    ToSSAForm().transform(prog)
}

// fn get_type(idx: usize, locals: &mut Vec<lir::Local>) -> Ty {
//     locals
//         .iter()
//         .find_map(|loc| {
//             if loc.idx == idx {
//                 Some(loc.ty.clone())
//             } else {
//                 None
//             }
//         })
//         .unwrap()
// }

// fn new_local(ty: Ty, locals: &mut Vec<lir::Local>) -> usize {
//     let new_idx = locals.len();
//     let loc = lir::Local::new(new_idx, ty);
//     locals.push(loc);
//     new_idx
// }

// fn replace_locals(insts: &mut [lir::Inst], orig: usize, new: usize) {
//     for inst in insts {
//         let locals = inst.get_locals_mut();
//         for loc in locals {
//             if *loc == orig {
//                 *loc = new;
//             }
//         }
//     }
// }

// fn visit_block(
//     block: &mut Vec<lir::Inst>,
//     locals: &mut Vec<lir::Local>,
//     use_set: &mut HashSet<usize>,
//     depth: usize,
// ) {
//     let mut i = 0;
//     let mut insts = std::mem::take(block);
//     while i < insts.len() {
//         let inst = &mut insts[i];
//         // let rest = &mut insts[(i + 1)..];
//         match inst {
//             lir::Inst::SetLocal(idx, _) => {
//                 if use_set.contains(idx) {
//                     // first create a new local for this instruction
//                     let orig_loc = *idx;
//                     let ty = get_type(orig_loc, locals);
//                     let new_loc = new_local(ty.clone(), locals);
//                     *idx = new_loc;
//                     use_set.insert(new_loc);

//                     if depth > 0 {
//                         // then create a new local for the phi instruction
//                         let phi_loc = new_local(ty, locals);
//                         block.push(lir::Inst::SetLocal(
//                             phi_loc,
//                             lir::Phi::new(orig_loc, new_loc).into(),
//                         ));

//                         // lastly, replace all of the references to the
//                         // original local with the new phi local
//                         replace_locals(&mut insts, orig_loc, phi_loc);
//                         use_set.insert(phi_loc);
//                     } else {
//                         replace_locals(&mut insts, orig_loc, new_loc);
//                     }
//                 } else {
//                     use_set.insert(*idx);
//                 }
//             }
//             lir::Inst::Block(block) => {
//                 visit_block(&mut block, locals, use_set, depth + 1);
//             }
//             lir::Inst::Loop(loop_stmt) => {
//                 visit_block(&mut loop_stmt.instructions, locals, use_set, depth + 1);
//             }
//             lir::Inst::Free(_)
//             | lir::Inst::Call(_)
//             | lir::Inst::CExternCall(_)
//             | lir::Inst::SetGlobal(_, _)
//             | lir::Inst::Func(_)
//             | lir::Inst::Store(_)
//             | lir::Inst::MemCopy(_, _, _)
//             | lir::Inst::IncRef(_, _)
//             | lir::Inst::DecRef(_)
//             | lir::Inst::Return(_)
//             | lir::Inst::If(_)
//             | lir::Inst::Break(_)
//             | lir::Inst::Goto(_)
//             | lir::Inst::Halt => {}
//         }

//         i += 1;
//     }

//     block.extend(insts);
// }
