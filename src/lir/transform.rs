use super::{Block, Func, Inst, Program};

pub trait Transform {
    type Ctx;

    fn transform(&mut self, prog: &mut Program) {
        for func in prog.funcs.iter_mut() {
            self.transform_func(func);
        }
    }

    fn transform_func(&mut self, func: &mut Func);
    fn transform_block(&mut self, block: &mut Block, ctx: &Self::Ctx);
    fn transform_inst(&mut self, inst: &mut Inst, ctx: &Self::Ctx);
}
