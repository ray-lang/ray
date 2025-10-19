use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

use crate::{
    constraint::InfoDetail,
    interface::{basic::HasBasic, subst::HasSubst, type_inference::HasTypeInference},
    types::{mgu_with_synonyms, Subst, Ty},
    TyVar,
};

mod basic;
mod overloading;

pub use basic::*;
pub use overloading::*;

pub trait HasState<T> {
    fn state(&self) -> &T;
    fn state_mut(&mut self) -> &mut T;
}

impl<A, I, T, V> HasSubst<I, T, V> for A
where
    A: HasState<SimpleState<T, V>> + HasBasic<I, T, V> + HasTypeInference<I, T, V>,
    I: Clone + InfoDetail,
    T: Display + Ty<V>,
    V: Display + TyVar + 'static,
{
    fn make_subst_consistent(&mut self) {
        // do nothing
    }

    fn unify_terms(&mut self, info: &I, lhs: &T, rhs: &T) {
        let synonyms = self.type_synonyms();
        let mut lhs = lhs.clone();
        lhs.apply_subst_from(self);
        let mut rhs = rhs.clone();
        rhs.apply_subst_from(self);
        match mgu_with_synonyms(&lhs, &rhs, &Subst::new(), synonyms) {
            Ok((_, subst)) => {
                self.state_mut().union(subst);
            }
            Err(err) => {
                let mut info = info.clone();
                info.add_detail(&err.to_string());
                self.add_labeled_err("unification", info)
            }
        }
    }

    fn get_subst(&self) -> &Subst<V, T> {
        &self.state()
    }

    fn get_subst_mut(&mut self) -> &mut Subst<V, T> {
        self.state_mut().deref_mut()
    }

    fn find_subst_for_var(&self, var: &V) -> T {
        self.state().lookup_var(var)
    }
}

#[derive(Debug, Default, Clone)]
pub struct SimpleState<T, V>(Subst<V, T>)
where
    T: Ty<V>,
    V: TyVar;

impl<T, V> Deref for SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = Subst<V, T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, V> DerefMut for SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, V> SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn to_subst(self) -> Subst<V, T> {
        self.0
    }
}
