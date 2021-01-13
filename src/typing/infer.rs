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
};

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

    pub fn infer_ty(&mut self, ex: &HirNode) -> Result<(), Vec<InferError>> {
        let mono_tys = HashSet::new();
        let (_, _, c) = ex.collect_constraints(&mono_tys, &mut self.ctx.tf_mut());
        let constraints = c.spread().phase().flatten(BottomUpWalk);
        println!("constraints: {:?}", constraints);

        let solver = GreedySolver::new(constraints, &mut self.ctx);
        let (solution, constraints) = solver.solve();

        // verify satisibility of the constraints using the solution
        println!("subst = {:?}", solution.subst);
        let errs = solution.satisfies(constraints, &self.ctx);

        println!("{:?}", solution);

        if errs.len() != 0 {
            Err(errs)
        } else {
            Ok(())
        }
    }
}
