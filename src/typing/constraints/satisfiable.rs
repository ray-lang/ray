use crate::typing::{
    predicate::PredicateEntails,
    solvers::Solution,
    traits::{Generalize, HasFreeVars},
    ty::Ty,
    ApplySubst, InferError, TyCtx,
};

use super::{
    AssumeConstraint, Constraint, ConstraintKind, EqConstraint, GenConstraint, ImplicitConstraint,
    InstConstraint, ProveConstraint, SkolConstraint, VarConstraint,
};

pub trait Satisfiable {
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError>;
}

impl Satisfiable for EqConstraint {
    fn satisfied_by(self, _: &Solution, _: &TyCtx) -> Result<(), InferError> {
        let EqConstraint(s, t) = self;
        if s != t {
            log::debug!(
                "equality constraint not satisified for types {} and {}",
                s,
                t
            );
            Err(InferError {
                msg: format!("types `{}` and `{}` are not equal", s, t),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for VarConstraint {
    fn satisfied_by(self, solution: &Solution, _: &TyCtx) -> Result<(), InferError> {
        let VarConstraint(v, t) = self;
        let u = solution.get_var(&v)?;
        if t != u {
            log::debug!(
                "variable constraint not satisified for types {} and {}",
                t,
                u
            );
            Err(InferError {
                msg: format!("types `{}` and `{}` are not equal", t, u),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for GenConstraint {
    fn satisfied_by(self, solution: &Solution, _: &TyCtx) -> Result<(), InferError> {
        log::debug!("gen constraint: {:?}", self);
        let GenConstraint(m, s, t) = self;
        let mut s: Ty = solution.get_ty(Ty::Var(s))?.apply_subst(&solution.subst);
        if !s.has_unknowns() {
            s = s.unquantify().unqualify();
        }
        let t = t
            .generalize(&m, &solution.preds)
            .apply_subst(&solution.subst);
        if s != t {
            log::debug!(
                "generalization constraint not satisified for types {} and {}",
                s,
                t
            );
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
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        log::debug!("inst constraint: {:?}", self);
        let InstConstraint(t, u) = self;
        let tyvars = t.free_vars().into_iter().cloned().collect::<Vec<_>>();
        let t = t.qualify(&solution.preds, &tyvars);
        let u = solution.get_ty(u)?;
        if !ctx.instance_of(&t, &u) {
            Err(InferError {
                msg: format!("type `{}` is not an instance of type `{}`", t, u),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for SkolConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        log::debug!("skol constraint: {:?}", self);
        let SkolConstraint(m, t, u) = self;
        let u = solution.get_ty(u)?;
        let t = t.generalize(
            &m.into_iter().map(|v| Ty::Var(v)).collect(),
            &solution.preds,
        );
        if !ctx.instance_of(&t, &u) {
            Err(InferError {
                msg: format!("type `{}` is not an instance of type `{}`", t, u),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for ImplicitConstraint {
    fn satisfied_by(self, _: &Solution, _: &TyCtx) -> Result<(), InferError> {
        todo!()
    }
}

impl Satisfiable for ProveConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        let p = self.get_predicate();
        if !solution.preds.entails(&p, ctx) {
            Err(InferError {
                msg: format!("expression does not {}", p.desc()),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for AssumeConstraint {
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        let p = self.get_predicate();
        if !solution.preds.entails(&p, ctx) {
            Err(InferError {
                msg: format!("expression does not {}", p.desc()),
                src: vec![],
            })
        } else {
            Ok(())
        }
    }
}

impl Satisfiable for ConstraintKind {
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        match self {
            ConstraintKind::Eq(c) => c.satisfied_by(solution, ctx),
            ConstraintKind::Var(c) => c.satisfied_by(solution, ctx),
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
    fn satisfied_by(self, solution: &Solution, ctx: &TyCtx) -> Result<(), InferError> {
        let src = self.info.src.iter().map(|src| src.clone()).collect();
        self.kind.satisfied_by(solution, ctx).map_err(|mut e| {
            e.src = src;
            e
        })
    }
}
