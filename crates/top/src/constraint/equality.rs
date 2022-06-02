use crate::{
    interface::{subst::HasSubst, type_inference::HasTypeInference},
    types::{Subst, Substitutable, Ty},
};

use super::{Solvable, TypeConstraintInfo};

#[derive(Debug)]
pub struct EqualityConstraint<T> {
    pub lhs: Ty,
    pub rhs: Ty,
    pub info: T,
}

impl<T> std::fmt::Display for EqualityConstraint<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} == {}", self.lhs, self.rhs)
    }
}

impl<Info> Substitutable for EqualityConstraint<Info> {
    fn apply_subst(&mut self, subst: &Subst) {
        self.lhs.apply_subst(subst);
        self.rhs.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<u32> {
        self.lhs
            .free_vars()
            .into_iter()
            .chain(self.rhs.free_vars())
            .collect()
    }
}

impl<State, T> Solvable<State> for EqualityConstraint<T>
where
    State: HasTypeInference<T> + HasSubst<T>,
    T: std::fmt::Display + TypeConstraintInfo<T>,
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
        syn.expand_type(&lhs) == syn.expand_type(&rhs)
    }
}

impl<Info> EqualityConstraint<Info> {
    pub fn new(lhs: Ty, rhs: Ty, info: Info) -> Self {
        EqualityConstraint { lhs, rhs, info }
    }
}
