use std::{
    collections::{HashMap, VecDeque},
    ops::{Deref, DerefMut},
};

use crate::typing::ty::{Ty, TyVar};

#[derive(Clone, Debug, PartialEq, Eq)]
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

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(k, v)| ((k.to_string(), v.to_string()))))
            .finish()
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

    // pub fn union_inplace<F>(&mut self, other: Subst, on_conflict: F)
    // where
    //     F: Fn(&TyVar, &Ty, &Ty) -> Ty + Copy,
    // {
    //     for (tv, ty) in other.0 {
    //         let mut ty = ty.apply_subst(&self);
    //         if let Some(other_ty) = self.get(&tv) {
    //             ty = on_conflict(self, &tv, &ty, &other_ty);
    //         }

    //         self.insert(tv, ty);
    //     }
    // }

    pub fn try_union_inplace<F, E>(&mut self, other: Subst, on_conflict: F) -> Result<(), E>
    where
        F: Fn(&Ty, &Ty) -> Result<Subst, E> + Copy,
    {
        for (tv, ty) in other.0 {
            let mut ty = ty.apply_subst(&self);
            if let Some(other_ty) = self.get(&tv) {
                let s = on_conflict(&ty, &other_ty)?;
                self.try_union_inplace(s, on_conflict)?;
                ty = ty.apply_subst(&self);
            }

            self.insert(tv, ty);
        }

        Ok(())
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
