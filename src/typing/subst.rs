use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
    ops::{Deref, DerefMut},
};

use crate::{
    typing::ty::{Ty, TyVar},
    utils::join,
};

use super::{
    predicate::TyPredicate,
    traits::{CollectTyVars, QualifyTypes, QuantifyTypes},
};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Subst(HashMap<TyVar, Ty>);

impl Deref for Subst {
    type Target = HashMap<TyVar, Ty>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Subst {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl AsRef<HashMap<TyVar, Ty>> for Subst {
    fn as_ref(&self) -> &HashMap<TyVar, Ty> {
        &self.0
    }
}

impl AsMut<HashMap<TyVar, Ty>> for Subst {
    fn as_mut(&mut self) -> &mut HashMap<TyVar, Ty> {
        &mut self.0
    }
}

impl IntoIterator for Subst {
    type Item = (TyVar, Ty);

    type IntoIter = std::collections::hash_map::IntoIter<TyVar, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<(TyVar, Ty)> for Subst {
    fn from_iter<T: IntoIterator<Item = (TyVar, Ty)>>(iter: T) -> Self {
        Subst(iter.into_iter().collect())
    }
}

impl std::fmt::Debug for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(k, v)| ((k.to_string(), v.to_string()))))
            .finish()
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Subst {
    pub fn new() -> Subst {
        Subst(HashMap::new())
    }

    pub fn from_types<P, A>(params: P, args: A) -> Subst
    where
        P: IntoIterator<Item = TyVar> + std::fmt::Debug,
        A: IntoIterator<Item = Ty> + std::fmt::Debug,
    {
        let mut sub = Subst::new();
        for (p, a) in params.into_iter().zip(args.into_iter()) {
            sub.insert(p, a);
        }
        sub
    }

    pub fn get_ty_for_var(&self, v: &TyVar) -> Ty {
        let mut cache = HashMap::new();
        self.get_ty_for_var_(v, &mut cache)
    }

    fn get_ty_for_var_(&self, v: &TyVar, cache: &mut HashMap<TyVar, Ty>) -> Ty {
        if let Some(t) = cache.get(v) {
            return t.clone();
        }

        // log::debug!("get ty for var: {}", v);
        let mut checked = HashSet::new();
        let mut var = v.clone();
        let mut ty = Ty::Var(var.clone());
        loop {
            checked.insert(var.clone());
            if let Some(t) = self.get(&var) {
                if let Ty::Var(u) = t {
                    if checked.contains(&u) {
                        break;
                    }
                    var = u.clone();
                    ty = Ty::Var(var.clone());
                } else {
                    ty = t.clone();
                    let unknowns = t.collect_tyvars();
                    // .into_iter()
                    // .filter(|u| !checked.contains(u))
                    // .collect::<Vec<_>>();
                    if unknowns.len() != 0 {
                        // log::debug!("ty = {}", t);
                        // log::debug!("unknowns: [{}]", join(&unknowns, ", "));
                        let sub = unknowns
                            .into_iter()
                            .map(|v| {
                                let u = self.get_ty_for_var(&v);
                                (v, u)
                            })
                            .collect::<Subst>();
                        // log::debug!("sub: {:?}", sub);
                        ty = ty.apply_subst(&sub);
                    }
                    break;
                }
            } else {
                break;
            }
        }

        cache.insert(v.clone(), ty.clone());
        ty
    }

    pub fn get_var(&self, v: TyVar) -> TyVar {
        let mut checked = HashSet::new();
        let mut v = v;
        loop {
            checked.insert(v.clone());
            if let Some(t) = self.get(&v) {
                if let Ty::Var(u) = t {
                    if checked.contains(&u) {
                        break;
                    }
                    v = u.clone();
                    continue;
                }
            }

            break;
        }

        v
    }

    pub fn union(mut self, other: Subst) -> Subst {
        self.union_inplace(other);
        self
    }

    pub fn union_inplace(&mut self, other: Subst) {
        for (tv, ty) in other.0 {
            let ty = ty.apply_subst(&self);
            log::debug!("union_inplace: {} => {}", tv, ty);
            let other_ty = self.get_ty_for_var(&tv);
            log::debug!("union_inplace: {} => {}", tv, other_ty);
            if !matches!(&other_ty, Ty::Var(other_var) if other_var == &tv) {
                if let Ty::Var(other_tv) = other_ty {
                    self.insert(other_tv, ty.clone());
                } else {
                    continue;
                }
            }

            self.insert(tv, ty);
        }
    }

    pub fn union_on_conflict<F>(&mut self, other: Subst, mut on_conflict: F)
    where
        F: FnMut(&Ty, &Ty),
    {
        for (tv, ty) in other.0 {
            let mut ty = ty.apply_subst(&self);
            if let Some(other_ty) = self.get(&tv) {
                on_conflict(&ty, &other_ty);
                ty = ty.apply_subst(&self);
            }

            self.insert(tv, ty);
        }
    }
}

impl QualifyTypes for Subst {
    fn qualify_tys(&mut self, preds: &Vec<TyPredicate>) {
        self.values_mut().qualify_tys(preds);
    }
}

impl QuantifyTypes for Subst {
    fn quantify_tys(&mut self) {
        self.values_mut().quantify_tys();
    }
}

pub trait ApplySubst<T = Self> {
    fn apply_subst(self, subst: &Subst) -> T;
}

pub trait ApplySubstMut {
    fn apply_subst_mut(&mut self, subst: &Subst);
}

impl<T: ApplySubst> ApplySubstMut for T {
    fn apply_subst_mut(&mut self, subst: &Subst) {
        unsafe {
            let old_t = std::mem::replace(self, std::mem::MaybeUninit::uninit().assume_init());
            let new_t = old_t.apply_subst(subst);
            let uninit = std::mem::replace(self, new_t);
            std::mem::forget(uninit);
        }
    }
}

impl ApplySubst for Subst {
    fn apply_subst(self, subst: &Subst) -> Subst {
        let mut this = self;
        for (_, v) in this.iter_mut() {
            v.apply_subst_mut(subst);
        }
        this
    }
}

impl<'a, T: ApplySubst> ApplySubst for &'a mut T {
    fn apply_subst(self, subst: &Subst) -> Self {
        self.apply_subst_mut(subst);
        self
    }
}

impl<T: ApplySubst> ApplySubst for Box<T> {
    fn apply_subst(self, subst: &Subst) -> Box<T> {
        Box::new((*self).apply_subst(subst))
    }
}

impl<T: ApplySubst> ApplySubst for Option<T> {
    fn apply_subst(self, subst: &Subst) -> Self {
        self.map(|t| t.apply_subst(subst))
    }
}

impl<T: ApplySubst> ApplySubst for Vec<T> {
    fn apply_subst(self, subst: &Subst) -> Vec<T> {
        self.into_iter().map(|x| x.apply_subst(subst)).collect()
    }
}

impl<T: ApplySubst> ApplySubst for VecDeque<T> {
    fn apply_subst(self, subst: &Subst) -> VecDeque<T> {
        self.into_iter().map(|x| x.apply_subst(subst)).collect()
    }
}

impl<T: ApplySubst> ApplySubst for Vec<(String, T)> {
    fn apply_subst(self, subst: &Subst) -> Vec<(String, T)> {
        self.into_iter()
            .map(|(n, t)| (n, t.apply_subst(subst)))
            .collect()
    }
}
