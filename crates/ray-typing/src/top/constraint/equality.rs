use std::{fmt::Display, marker::PhantomData};

use crate::top::{
    TyVar,
    interface::{subst::HasSubst, type_inference::HasTypeInference},
    types::{Subst, Substitutable, Ty},
};

use super::{Solvable, TypeConstraintInfo};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqualityConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub lhs: T,
    pub rhs: T,
    pub info: I,
    _phantom: PhantomData<V>,
}

impl<I, T, V> Display for EqualityConstraint<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} == {}", self.lhs, self.rhs)
    }
}

impl<I, T, V> Substitutable<V, T> for EqualityConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        self.lhs.apply_subst(subst);
        self.rhs.apply_subst(subst);
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        self.lhs.apply_subst_all(subst);
        self.rhs.apply_subst_all(subst);
    }

    fn free_vars(&self) -> Vec<&V> {
        self.lhs
            .free_vars()
            .into_iter()
            .chain(self.rhs.free_vars())
            .collect()
    }
}

impl<State, I, T, V> Solvable<State, T, V> for EqualityConstraint<I, T, V>
where
    State: HasTypeInference<I, T, V> + HasSubst<I, T, V>,
    I: Display + TypeConstraintInfo<I, T, V>,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn solve(&mut self, state: &mut State) {
        self.info.equality_type_pair(&self.lhs, &self.rhs);
        state.unify_terms(&self.info, &self.lhs, &self.rhs);
    }

    fn check_condition(&self, state: &State) -> bool {
        let mut lhs = self.lhs.clone();
        lhs.apply_subst_from(state);
        let mut rhs = self.rhs.clone();
        rhs.apply_subst_from(state);
        let syn = state.type_synonyms();
        syn.expand_type(lhs) == syn.expand_type(rhs)
    }
}

impl<I, T, V> EqualityConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new(lhs: T, rhs: T, info: I) -> Self {
        EqualityConstraint {
            lhs,
            rhs,
            info,
            _phantom: PhantomData,
        }
    }
}
