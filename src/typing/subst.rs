use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter::FromIterator,
    ops::{Deref, DerefMut},
};

use crate::typing::ty::{Ty, TyVar};

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

    pub fn get_var(&self, v: &TyVar) -> Ty {
        let mut checked = HashSet::new();

        let mut v = v.clone();
        loop {
            checked.insert(v.clone());
            if let Some(t) = self.get(&v) {
                if let Ty::Var(u) = t {
                    if checked.contains(&u) {
                        break;
                    }
                    v = u.clone();
                } else if t.has_unknowns() {
                    return t.clone().apply_subst(self);
                } else {
                    return t.clone();
                }
            } else {
                break;
            }
        }

        Ty::Var(v)
    }

    pub fn union(mut self, other: Subst) -> Subst {
        for (tv, ty) in other.0 {
            let ty = ty.apply_subst(&self);
            if let Some(other_ty) = self.get(&tv).cloned() {
                if let Ty::Var(other_tv) = other_ty {
                    self.insert(other_tv, ty.clone());
                } else if let Ty::Var(tv) = ty {
                    self.insert(tv, other_ty);
                    continue;
                }
            }

            self.insert(tv, ty);
        }
        self
    }

    pub fn union_inplace<F>(&mut self, other: Subst, mut on_conflict: F)
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

pub trait ApplySubst<T = Self> {
    fn apply_subst(self, subst: &Subst) -> T;
}

pub trait ApplySubstMut {
    fn apply_subst_mut(&mut self, subst: &Subst);
}

impl<T: ApplySubst + Clone> ApplySubstMut for T {
    fn apply_subst_mut(&mut self, subst: &Subst) {
        let t = self.clone();
        let _ = std::mem::replace(self, t.apply_subst(subst));
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

impl<T: ApplySubst> ApplySubst<Box<T>> for Box<T> {
    fn apply_subst(self, subst: &Subst) -> Box<T> {
        Box::new((*self).apply_subst(subst))
    }
}

impl<T: ApplySubst> ApplySubst<Vec<T>> for Vec<T> {
    fn apply_subst(self, subst: &Subst) -> Vec<T> {
        self.into_iter().map(|x| x.apply_subst(subst)).collect()
    }
}

impl<T: ApplySubst> ApplySubst<VecDeque<T>> for VecDeque<T> {
    fn apply_subst(self, subst: &Subst) -> VecDeque<T> {
        self.into_iter().map(|x| x.apply_subst(subst)).collect()
    }
}

impl<T: ApplySubst> ApplySubst<Vec<(String, T)>> for Vec<(String, T)> {
    fn apply_subst(self, subst: &Subst) -> Vec<(String, T)> {
        self.into_iter()
            .map(|(n, t)| (n, t.apply_subst(subst)))
            .collect()
    }
}
