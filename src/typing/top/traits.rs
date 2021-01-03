use std::collections::{HashMap, HashSet};

use crate::typing::{
    ty::{Ty, TyVar},
    Subst,
};

use super::constraints::{Constraint, ConstraintInfo};

pub trait HasBasic {
    fn add_constraint(&mut self, c: Constraint);

    fn add_constraints(&mut self, cs: Vec<Constraint>);

    fn pop_constraint(&mut self) -> Option<Constraint>;

    fn add_error(&mut self, info: ConstraintInfo);

    fn get_errors(&self) -> Vec<ConstraintInfo>;

    fn add_check<F>(&mut self, msg: String, check: F)
    where
        F: Fn() -> bool;
}

pub trait HasSubst {
    fn apply_subst(&mut self);

    fn get_subst(&self) -> &Subst;

    fn unify_terms(&mut self, s: &Ty, t: &Ty) -> Result<(), String>;

    fn make_consistent(&mut self);

    fn subst_var(&mut self, v: TyVar, ty: Ty);
}

pub trait HasState {
    fn next_tvar(&mut self) -> TyVar;

    fn next_svar(&mut self) -> TyVar;

    fn instantiate(&mut self, ty: Ty, reverse_subst: &mut HashMap<TyVar, TyVar>) -> Ty;

    // fn get_ty_syn(&self) -> TySynonyms;

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo);

    fn lookup_ty(&self, v: &TyVar) -> Ty;

    fn find_ty(&self, r: &Ty) -> Ty;

    fn add_skolems(&mut self, info: &ConstraintInfo, skolems: Vec<TyVar>, tyvars: Vec<TyVar>);
}

pub trait HasFreeVars {
    fn free_vars(&self) -> HashSet<&TyVar>;
}

pub trait PolymorphismInfo {
    fn inst_ty(self, ty: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }

    fn skol_ty(self, ty: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }
}

pub trait Generalize {
    fn generalize(self, m: &Vec<Ty>) -> Self;
}

pub trait Skolemize {
    fn skolemize(&self) -> (Self, Vec<TyVar>)
    where
        Self: Sized;
}

pub trait TreeWalk<A>: Copy {
    fn walk(self, down: Vec<A>, pairs: Vec<(Vec<A>, Vec<A>)>) -> Vec<A>;
}
