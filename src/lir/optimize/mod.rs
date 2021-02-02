mod inline;
mod redundant_assign;

use crate::lir;

use inline::Inline;
use redundant_assign::RedundantAssignElim;

pub trait Optimize {
    fn level(&self) -> usize;

    fn optimize_func(&self, func: &mut lir::Func);

    fn optimize(&self, prog: &mut lir::Program) {
        for func in prog.funcs.iter_mut() {
            self.optimize_func(func)
        }
    }
}

struct Optimizer<'a> {
    passes: Vec<&'a dyn Optimize>,
}

pub fn optimize(prog: &mut lir::Program, _max_level: usize) {
    let mut opt = Optimizer::new();

    // add passes
    opt.passes.push(&Inline());
    opt.passes.push(&RedundantAssignElim());

    opt.optimize(prog);
}

impl<'a> Optimizer<'a> {
    fn new() -> Optimizer<'a> {
        Optimizer { passes: vec![] }
    }

    fn optimize(&self, prog: &mut lir::Program) {
        for pass in self.passes.iter() {
            pass.optimize(prog);
        }
    }
}
