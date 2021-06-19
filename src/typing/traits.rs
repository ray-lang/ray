use std::collections::{HashMap, HashSet};

use crate::{
    convert::ToSet,
    typing::{
        predicate::TyPredicate,
        ty::{Ty, TyVar},
        Subst,
    },
};

use super::{
    constraints::{Constraint, ConstraintInfo, ConstraintList},
    state::TyVarFactory,
    TyCtx,
};

pub trait HasType {
    fn ty(&self) -> Ty;
}

impl<T> HasType for Box<T>
where
    T: HasType,
{
    fn ty(&self) -> Ty {
        self.as_ref().ty()
    }
}

pub trait HasBasic {
    fn ctx(&self) -> &TyCtx;

    fn get_constraints_mut(&mut self) -> &mut ConstraintList;

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

    fn get_var(&self, v: &Ty) -> Ty;
}

pub trait HasState {
    fn tf(&mut self) -> &mut TyVarFactory;

    fn sf(&mut self) -> &mut TyVarFactory;

    fn store_ty(&mut self, v: TyVar, ty: Ty, info: ConstraintInfo);

    fn inst_ty(&mut self, v: Ty, u: Ty);

    fn skol_ty(&mut self, v: Ty, u: Ty);

    fn lookup_ty(&self, tv: &TyVar) -> Option<Ty>;

    fn find_ty(&self, r: &Ty) -> Ty;

    fn add_skolems(&mut self, info: &ConstraintInfo, skolems: Vec<TyVar>, monos: Vec<TyVar>);
}

pub trait HasPredicates {
    fn get_preds(&self) -> Vec<&(TyPredicate, ConstraintInfo)>;

    fn assume_pred(&mut self, p: TyPredicate, info: ConstraintInfo);

    fn prove_pred(&mut self, p: TyPredicate, info: ConstraintInfo);

    fn generalize_with_preds(&mut self, mono_tys: &Vec<Ty>, ty: Ty) -> Ty;
}

pub trait QualifyTypes {
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>);
}

impl<'a> QualifyTypes for std::vec::IntoIter<&'a mut Ty> {
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
        for t in self {
            if t.is_func() {
                t.qualify_in_place(preds);
            }
        }
    }
}

impl<'a, K> QualifyTypes for std::collections::hash_map::ValuesMut<'a, K, Ty> {
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
        for t in self {
            if t.is_func() {
                t.qualify_in_place(preds);
            }
        }
    }
}

impl<'a, T> QualifyTypes for Vec<T>
where
    T: QualifyTypes,
{
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
        for t in self.iter_mut() {
            t.qualify_tys(preds);
        }
    }
}

pub trait QuantifyTypes {
    fn quantify_tys(&mut self);
}

impl<'a> QuantifyTypes for std::vec::IntoIter<&'a mut Ty> {
    fn quantify_tys(&mut self) {
        for t in self {
            if t.is_func() {
                t.quantify_in_place();
            }
        }
    }
}

impl<'a, K> QuantifyTypes for std::collections::hash_map::ValuesMut<'a, K, Ty> {
    fn quantify_tys(&mut self) {
        for t in self {
            if t.is_func() {
                t.quantify_in_place();
            }
        }
    }
}

impl<'a, T> QuantifyTypes for Vec<T>
where
    T: QuantifyTypes,
{
    fn quantify_tys(&mut self) {
        for t in self.iter_mut() {
            t.quantify_tys();
        }
    }
}

pub trait CollectTyVars {
    fn collect_tyvars(&self) -> Vec<TyVar>;
}

impl<T> CollectTyVars for Vec<T>
where
    T: CollectTyVars,
{
    fn collect_tyvars(&self) -> Vec<TyVar> {
        self.iter().flat_map(|t| t.collect_tyvars()).collect()
    }
}

pub trait HasFreeVars {
    fn free_vars(&self) -> HashSet<&TyVar>;
}

impl<T> HasFreeVars for Vec<T>
where
    T: HasFreeVars,
{
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.iter().flat_map(|t| t.free_vars()).to_set()
    }
}

impl<S, T> HasFreeVars for Vec<(S, T)>
where
    T: HasFreeVars,
{
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.iter().flat_map(|(_, t)| t.free_vars()).to_set()
    }
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
    fn inst_ty(self, _: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }

    fn skol_ty(self, _: &Ty) -> Self
    where
        Self: Sized,
    {
        self
    }
}

pub trait Polymorphize {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self;
}

impl<T: Polymorphize> Polymorphize for Vec<T> {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
        self.into_iter()
            .map(|t| t.polymorphize(tf, subst))
            .collect()
    }
}

impl<T: Polymorphize> Polymorphize for Box<T> {
    fn polymorphize(self, tf: &mut TyVarFactory, subst: &mut HashMap<Ty, TyVar>) -> Self {
        let t = *self;
        Box::new(t.polymorphize(tf, subst))
    }
}

pub trait Instantiate {
    fn instantiate(self, tf: &mut TyVarFactory) -> Self;
}

impl<T: Instantiate> Instantiate for Box<T> {
    fn instantiate(self, tf: &mut TyVarFactory) -> Self {
        let t = *self;
        Box::new(t.instantiate(tf))
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

pub trait TreeWalk: Copy {
    fn walk(
        self,
        down: Vec<Constraint>,
        pairs: Vec<(Vec<Constraint>, Vec<Constraint>)>,
    ) -> Vec<Constraint>;
}
