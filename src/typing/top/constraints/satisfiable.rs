use crate::{
    typing::{
        predicate::PredicateEntails,
        top::{
            solvers::Solution,
            traits::{Generalize, HasFreeVars},
        },
        ty::Ty,
        ApplySubst, Ctx, InferError,
    },
    utils::join,
};

use super::{
    AssumeConstraint, Constraint, ConstraintKind, EqConstraint, GenConstraint, ImplicitConstraint,
    InstConstraint, ProveConstraint, SkolConstraint,
};

pub trait Satisfiable {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError>;
}

impl Satisfiable for EqConstraint {
    fn satisfied_by(self, _: &Solution, _: &Ctx) -> Result<(), InferError> {
        let EqConstraint(s, t) = self;
        if s != t {
            println!("EqConstraint: s = {:?}", s);
            println!("EqConstraint: t = {:?}", t);
            Err(InferError {
                msg: format!("types `{}` and `{}` are not equal", s, t),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for GenConstraint {
    fn satisfied_by(self, solution: &Solution, _: &Ctx) -> Result<(), InferError> {
        let GenConstraint(m, s, t) = self;
        let s = solution.get_ty(Ty::Var(s))?;
        println!("s = {}", s);
        println!("preds = {{{}}}", join(&solution.preds, ", "));
        let t = t.generalize(&m, &solution.preds);
        println!("t = {}", t);
        if s != t {
            Err(InferError {
                msg: format!("types `{}` and `{}` are not equal", s, t),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for InstConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        let InstConstraint(t, u) = self;
        let tyvars = t.free_vars().into_iter().cloned().collect::<Vec<_>>();
        println!("pre-qualified: {}", t);
        let t = t.qualify_with_tyvars(&solution.preds, &tyvars);
        println!("    qualified: {}", t);
        let u = solution.get_ty(u)?;
        if !ctx.instance_of(&t, &u) {
            Err(InferError {
                msg: format!("type `{}` is not an instance of `{}`", t, u),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for SkolConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        let SkolConstraint(m, t, u) = self;
        let u = solution.get_ty(u)?;
        let t = t.generalize(
            &m.into_iter().map(|v| Ty::Var(v)).collect(),
            &solution.preds,
        );
        if !ctx.instance_of(&t, &u) {
            Err(InferError {
                msg: format!("type `{}` is not an instance of type `{}`", u, t),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for ImplicitConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        todo!()
    }
}

impl Satisfiable for ProveConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        let p = self.get_predicate();
        if !solution.preds.entails(&p, ctx) {
            Err(InferError {
                msg: format!("`{}` cannot be met", p),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for AssumeConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        let p = self.get_predicate();
        if !solution.preds.entails(&p, ctx) {
            Err(InferError {
                msg: format!("`{}` cannot be met", p),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for ConstraintKind {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        println!("satisfied_by: {:?}", self);
        match self {
            ConstraintKind::Eq(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Gen(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Inst(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Skol(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Implicit(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Prove(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Assume(c) => c.satisfied_by(solution, ctx),
        }
    }
}

impl Satisfiable for Constraint {
    fn satisfied_by(self, solution: &Solution, ctx: &Ctx) -> Result<(), InferError> {
        let src = self.info.src.clone();
        self.kind.satisfied_by(solution, ctx).map_err(|mut e| {
            e.src = src;
            e
        })
    }
}
