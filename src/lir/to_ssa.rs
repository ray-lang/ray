use std::{
    collections::{HashMap, HashSet},
    marker::PhantomData,
};

use crate::lir;

use super::{ControlFlowGraph, Transform};

pub struct ToSSAForm();

pub type SSAContext = HashMap<String, Vec<(usize, usize)>>;

impl Transform for ToSSAForm {
    type Ctx = SSAContext;

    fn transform_func(&mut self, func: &mut lir::Func) {
        // log::debug!("BEFORE to ssa: {}", func);
        // let frontiers = func.calculate_dom_frontiers();

        // // look through each block and create a mapping where each local is assigned
        // let mut local_map = HashMap::<usize, Vec<usize>>::new();
        // for block in func.blocks.iter() {
        //     for inst in block.iter() {
        //         if let &lir::Inst::SetLocal(loc, _) = inst {
        //             local_map.entry(loc).or_default().push(block.label());
        //         }
        //     }
        // }

        // log::debug!("frontiers: {:?}", frontiers);

        // for loc in func.locals.iter() {
        //     if let Some(blocks) = local_map.get_mut(&loc.idx) {
        //         let mut idx = 0;
        //         while idx < blocks.len() {
        //             let label = blocks[idx];
        //             if let Some(succ_blocks) = frontiers.get(&label) {
        //                 // add a phi-node to each block in the dominance frontier
        //                 for &succ_label in succ_blocks {
        //                     let block = &mut func.blocks[succ_label];
        //                     block.phi(loc.idx, (succ_label, loc.idx));

        //                     // since this block now writes to the local,
        //                     // it needs to be added here
        //                     if !blocks.contains(&succ_label) {
        //                         blocks.push(succ_label);
        //                     }
        //                 }
        //             }

        //             idx += 1;
        //         }
        //     }
        // }

        // log::debug!("to ssa: {}", func);
    }

    fn transform_block(&mut self, block: &mut lir::Block, ctx: &Self::Ctx) {

        // let mut idx = 0;
        // while idx < block.len() {
        //     let inst = &mut block[idx];
        //     let remove = if let lir::Inst::SetLocal(_, lir::Value::VarRef(var)) = inst {
        //         // this means that this is the first definition of the variable;
        //         // in this case, we don't need this assignmnet
        //         ctx.get(var).is_none()
        //     } else {
        //         false
        //     };

        //     if remove {
        //         block.remove(idx);
        //         continue;
        //     }

        //     self.transform_inst(inst, ctx);
        //     idx += 1;
        // }
    }

    fn transform_inst(&mut self, inst: &mut lir::Inst, ctx: &Self::Ctx) {
        // if let lir::Inst::SetLocal(_, val) = inst {
        //     if let lir::Value::VarRef(var) = &val {
        //         // lookup the variable in the map
        //         let var = var.clone();
        //         if let Some(values) = ctx.get(&var).cloned() {
        //             if values.len() == 1 {
        //                 let (_, loc) = values[0];
        //                 *val = lir::Atom::Variable(lir::Variable::Local(loc)).into();
        //             } else {
        //                 *val = lir::Phi::new(values).into();
        //             }
        //         }
        //     }
        // }
    }
}

pub fn to_ssa(prog: &mut lir::Program) {
    ToSSAForm().transform(prog)
}
