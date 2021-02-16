use std::collections::HashSet;

use crate::span::{Source, SourceMap};

use super::{
    collect::CollectConstraints,
    constraints::tree::BottomUpWalk,
    context::TyCtx,
    solvers::{GreedySolver, Solution, Solver},
    ApplySubst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferError {
    pub msg: String,
    pub src: Vec<Source>,
}

#[derive(Debug)]
pub struct InferSystem<'tcx> {
    tcx: &'tcx mut TyCtx,
}

impl<'tcx> InferSystem<'tcx> {
    pub fn new(tcx: &'tcx mut TyCtx) -> InferSystem {
        InferSystem { tcx }
    }

    pub fn infer_ty<T, U>(
        &mut self,
        v: &T,
        srcmap: &mut SourceMap,
    ) -> Result<Solution, Vec<InferError>>
    where
        T: CollectConstraints<Output = U> + std::fmt::Display,
    {
        let mono_tys = HashSet::new();
        let (_, _, c) = v.collect_constraints(&mono_tys, srcmap, self.tcx);
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", v);
        log::debug!("constraints: {:#?}", constraints);

        let solver = GreedySolver::new(constraints, &mut self.tcx);
        let (solution, constraints) = solver.solve();

        log::debug!("solution (before satisfy check): {:#?}", solution);

        // verify satisibility of the constraints using the solution
        let errs = solution.satisfies(constraints, &self.tcx);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok(solution)
        }
    }
}
