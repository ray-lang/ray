use std::collections::HashSet;

use crate::span::Source;

use super::{
    collect::CollectConstraints,
    constraints::tree::BottomUpWalk,
    context::Ctx,
    solvers::{GreedySolver, Solution, Solver},
    ty::Ty,
    ApplySubst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferError {
    pub msg: String,
    pub src: Vec<Source>,
}

#[derive(Clone, Debug)]
pub struct InferSystem {
    ctx: Ctx,
}

impl InferSystem {
    pub fn new(ctx: Ctx) -> InferSystem {
        InferSystem { ctx }
    }

    pub fn infer_ty<T, U>(&mut self, v: T) -> Result<(U, Solution), Vec<InferError>>
    where
        T: CollectConstraints<Output = U>,
        U: std::fmt::Display + ApplySubst,
    {
        let mono_tys = HashSet::new();
        let (v, _, c) = v.collect_constraints(&mono_tys, &mut self.ctx.tf_mut());
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", v);
        log::debug!("constraints: {:#?}", constraints);

        let solver = GreedySolver::new(constraints, &mut self.ctx);
        let (mut solution, constraints) = solver.solve();

        log::debug!("solution (before satisfy check): {:#?}", solution);

        // verify satisibility of the constraints using the solution
        let errs = solution.satisfies(constraints, &self.ctx);

        // apply the substitution
        let v = v.apply_subst(&solution.subst);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok((v, solution))
        }
    }
}
