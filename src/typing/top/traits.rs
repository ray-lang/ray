use std::{
    cell::RefMut,
    collections::{HashMap, HashSet},
};

use crate::typing::{
    predicate::TyPredicate,
    ty::{Ty, TyVar},
    InferError, Subst,
};

use super::{
    constraints::{Constraint, ConstraintInfo},
    state::TyVarFactory,
};

pub trait HasBasic {
    fn get_constraints(&self) -> Vec<Constraint>;

    fn add_constraint(&mut self, c: Constraint);

    fn add_constraints(&mut self, cs: Vec<Constraint>);

    fn pop_constraint(&mut self) -> Option<Constraint>;

    fn add_error(&mut self, info: ConstraintInfo);

    fn get_errors(&self) -> Vec<ConstraintInfo>;
}

pub trait HasSubst {
    fn apply_subst(&mut self);

    fn get_subst(&self) -> &Subst;

    fn unify_terms(&mut self, s: &Ty, t: &Ty, info: &ConstraintInfo) -> bool;

    fn make_consistent(&mut self);

    fn subst_var(&mut self, v: TyVar, ty: Ty);
}

pub trait HasState {
    fn new_tvar(&mut self) -> TyVar;

    fn new_svar(&mut self) -> TyVar;

    fn get_tf(&mut self) -> RefMut<TyVarFactory>;

    fn get_sf(&mut self) -> RefMut<TyVarFactory>;

    // fn get_ty_syn(&self) -> TySynonyms;

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo);

    fn lookup_ty(&self, tv: &TyVar) -> Option<Ty>;

    fn find_ty(&self, r: &Ty) -> Ty;

    fn add_skolems(&mut self, info: &ConstraintInfo, skolems: Vec<TyVar>, monos: Vec<TyVar>);

    fn check_skolems(&mut self);
}

pub trait HasPredicates {
    fn get_preds(&self) -> &Vec<(TyPredicate, ConstraintInfo)>;

    // assumePredicate :: Predicate → ⟨i⟩ → m ()
    fn assume_pred(&mut self, p: TyPredicate, info: ConstraintInfo);

    // provePredicate :: Predicate → ⟨i⟩ → m ()
    fn prove_pred(&mut self, p: TyPredicate, info: ConstraintInfo);

    // contextReduction :: m ()
    fn ctx_reduce(&mut self);

    // generalizeWithPreds :: Monos → Type → m TypeScheme
    fn generalize_with_preds(&mut self, mono_tys: &Vec<Ty>, ty: Ty) -> Ty;

    // reportAmbiguous :: m ()
}

pub trait HasFreeVars {
    fn free_vars(&self) -> HashSet<&TyVar>;
}

pub trait FreezeVars {
    fn freeze_tyvars(self) -> Self;

    fn unfreeze_tyvars(self) -> Self;
}

impl<T> FreezeVars for Vec<T>
where
    T: FreezeVars,
{
    fn freeze_tyvars(self) -> Vec<T> {
        self.into_iter().map(|t| t.freeze_tyvars()).collect()
    }

    fn unfreeze_tyvars(self) -> Vec<T> {
        self.into_iter().map(|t| t.unfreeze_tyvars()).collect()
    }
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
    fn generalize(self, m: &Vec<Ty>, preds: &Vec<TyPredicate>) -> Self;
}

pub trait Skolemize {
    fn skolemize(&self, sf: &mut TyVarFactory) -> (Self, Vec<TyVar>)
    where
        Self: Sized;
}

pub trait TreeWalk<A>: Copy {
    fn walk(self, down: Vec<A>, pairs: Vec<(Vec<A>, Vec<A>)>) -> Vec<A>;
}
