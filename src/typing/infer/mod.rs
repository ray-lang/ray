use std::collections::HashSet;

use crate::span::Source;

use super::{
    collect::CollectConstraints,
    constraints::tree::BottomUpWalk,
    context::Ctx,
    solvers::{GreedySolver, Solver},
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

    pub fn infer_ty<T, U>(&mut self, v: T) -> Result<U, Vec<InferError>>
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
        log::debug!("constraints to check: {:#?}", constraints);

        log::debug!("solution: {:#?}", solution);

        solution.formalize_types();

        solution
            .preds
            .extend(solution.preds.clone().apply_subst(&solution.subst));
        solution.preds.sort();
        solution.preds.dedup();

        // verify satisibility of the constraints using the solution
        let errs = solution.satisfies(constraints, &self.ctx);

        // qualify all types in the substitution
        for t in solution.subst.values_mut() {
            if t.is_func() {
                let tyvars = t.collect_tyvars();
                let old_t = std::mem::replace(t, Ty::unit());
                *t = old_t.qualify_with_tyvars(&solution.preds, &tyvars);
            }
        }

        // apply the substitution
        let v = v.apply_subst(&solution.subst);

        log::debug!("solution: {:#?}", solution);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok(v)
        }
    }
}
