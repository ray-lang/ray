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
