use std::collections::HashSet;

use crate::{
    errors::{RayError, RayErrorKind},
    span::{Source, SourceMap},
    typing::state::TyEnv,
};

use super::{
    collect::{CollectConstraints, CollectCtx},
    constraints::tree::BottomUpWalk,
    context::TyCtx,
    solvers::{GreedySolver, Solution, Solver},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InferError {
    pub msg: String,
    pub src: Vec<Source>,
}

impl From<InferError> for RayError {
    fn from(err: InferError) -> Self {
        RayError {
            msg: err.msg,
            src: err.src,
            kind: RayErrorKind::Type,
        }
    }
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
        defs: TyEnv,
    ) -> Result<(Solution, TyEnv), Vec<InferError>>
    where
        T: CollectConstraints<Output = U> + std::fmt::Display,
    {
        let mono_tys = HashSet::new();
        let mut ctx = CollectCtx {
            mono_tys: &mono_tys,
            srcmap: &srcmap,
            tcx: self.tcx,
            defs,
        };
        let (_, _, c) = v.collect_constraints(&mut ctx);
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        log::debug!("{}", v);
        log::debug!("constraints: {:#?}", constraints);

        let defs = ctx.defs;
        let solver = GreedySolver::new(constraints, &mut self.tcx);
        let (solution, constraints) = solver.solve();

        log::debug!("solution (before satisfy check): {:#?}", solution);

        // verify satisibility of the constraints using the solution
        let errs = solution.satisfies(constraints, &self.tcx);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok((solution, defs))
        }
    }
}
