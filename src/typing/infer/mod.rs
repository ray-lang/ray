use std::collections::HashSet;

use crate::span::Source;

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

    pub fn infer_ty<T, U>(&mut self, v: T) -> Result<(U, Solution), Vec<InferError>>
    where
        T: CollectConstraints<Output = U>,
        U: std::fmt::Display + ApplySubst,
    {
        let mono_tys = HashSet::new();
        let (v, _, c) = v.collect_constraints(&mono_tys, &mut self.tcx.tf_mut());
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", v);
        log::debug!("constraints: {:#?}", constraints);

        let solver = GreedySolver::new(constraints, &mut self.tcx);
        let (solution, constraints) = solver.solve();

        log::debug!("solution (before satisfy check): {:#?}", solution);

        // verify satisibility of the constraints using the solution
        let errs = solution.satisfies(constraints, &self.tcx);

        // apply the substitution
        let v = v.apply_subst(&solution.subst);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok((v, solution))
        }
    }
}
