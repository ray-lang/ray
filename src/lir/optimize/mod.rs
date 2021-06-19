mod branch_elim;
mod inline;
mod minimize_locals;
mod redundant_assign;
mod simplify_phi;

use std::collections::{HashMap, HashSet};

use crate::{lir, span::SourceMap};

use inline::Inline;
use redundant_assign::RedundantAssignElim;
use simplify_phi::SimplifyPhiNodes;

use self::minimize_locals::MinimizeLocals;

use super::MapLocals;

pub trait Optimize {
    fn level(&self) -> usize;

    fn optimize_func(&self, func: &mut lir::Func);

    fn optimize(&self, prog: &mut lir::Program, _: &SourceMap) {
        for func in prog.funcs.iter_mut() {
            self.optimize_func(func)
        }
    }
}

struct Optimizer<'a> {
    passes: Vec<&'a dyn Optimize>,
}

pub fn optimize(prog: &mut lir::Program, srcmap: &SourceMap, _max_level: usize) {
    let mut opt = Optimizer::new();

    // add passes
    // opt.passes.push(&Inline());
    opt.passes.push(&SimplifyPhiNodes());
    opt.passes.push(&RedundantAssignElim());
    opt.passes.push(&MinimizeLocals());

    opt.optimize(prog, srcmap);
}

fn reindex_locals(func: &mut lir::Func, replaced: &HashSet<usize>) {
    // determine the locals that were _not_ replaced
    let locals = func.locals.drain(..).collect::<Vec<_>>();
    let mut reindex = HashMap::new();
    for (i, loc) in locals.into_iter().enumerate() {
        if !replaced.contains(&i) {
            let new_idx = func.locals.len();
            func.locals.push(loc);
            reindex.insert(i, new_idx);
        }
    }

    // reindex the locals
    func.map_locals(&reindex);
}

impl<'a> Optimizer<'a> {
    fn new() -> Optimizer<'a> {
        Optimizer { passes: vec![] }
    }

    fn optimize(&self, prog: &mut lir::Program, srcmap: &SourceMap) {
        for pass in self.passes.iter() {
            pass.optimize(prog, srcmap);
        }
    }
}
