use std::collections::HashSet;

use crate::{
    hir::{HirNode, TypedHirNode},
    span::Source,
};

use super::{
    context::Ctx,
    top::{
        collect::CollectConstraints,
        constraints::tree::BottomUpWalk,
        solvers::{GreedySolver, Solver},
    },
    ty::{Ty, TyVar},
    ApplySubst, Subst,
};

mod formalize;

pub use formalize::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferError {
    pub msg: String,
    pub src: Vec<Source>,
}

pub type InferResult = Result<(TypedHirNode, Ctx), InferError>;

#[derive(Clone, Debug)]
pub struct InferSystem {
    ctx: Ctx,
}

impl InferSystem {
    pub fn new(ctx: Ctx) -> InferSystem {
        InferSystem { ctx }
    }

    pub fn infer_ty(&mut self, ex: HirNode) -> Result<HirNode, Vec<InferError>> {
        let mono_tys = HashSet::new();
        let (ex, _, c) = ex.collect_constraints(&mono_tys, &mut self.ctx.tf_mut());
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", ex);
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
        let ex = ex.apply_subst(&solution.subst);

        log::debug!("solution: {:#?}", solution);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok(ex)
        }
    }
}
