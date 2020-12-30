use std::{
    collections::HashMap,
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
            if let Some(Ty::Var(other_tv)) = self.get(&tv).cloned() {
                self.insert(other_tv.clone(), ty.clone());
            }

            self.insert(tv, ty);
        }
        self
    }
}

pub trait ApplySubst<T = Self> {
    fn apply_subst(self, subst: &Subst) -> T;
}
