mod equality;
mod info;
mod polymorphism;

pub use equality::*;
pub use info::*;
pub use polymorphism::*;

use crate::{
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{Subst, Substitutable},
};

pub trait Solvable<State>
where
    Self: std::fmt::Display + Substitutable,
{
    fn solve(&mut self, state: &mut State);

    fn check_condition(&self, _state: &State) -> bool {
        true
    }
}

#[derive(Debug)]
pub enum Constraint<T> {
    Equality(EqualityConstraint<T>),
    Polymorphism(PolymorphismConstraint<T>),
}

impl<T> std::fmt::Display for Constraint<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Constraint::Equality(c) => write!(f, "{}", c),
            Constraint::Polymorphism(c) => write!(f, "{}", c),
        }
    }
}

impl<T> From<EqualityConstraint<T>> for Constraint<T> {
    fn from(c: EqualityConstraint<T>) -> Self {
        Constraint::Equality(c)
    }
}

impl<T> From<PolymorphismConstraint<T>> for Constraint<T> {
    fn from(c: PolymorphismConstraint<T>) -> Self {
        Constraint::Polymorphism(c)
    }
}

impl<T> Substitutable for Constraint<T> {
    fn apply_subst(&mut self, subst: &Subst) {
        match self {
            Constraint::Equality(c) => c.apply_subst(subst),
            Constraint::Polymorphism(c) => c.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        match self {
            Constraint::Equality(c) => c.free_vars(),
            Constraint::Polymorphism(c) => c.free_vars(),
        }
    }
}

impl<State, T> Solvable<State> for Constraint<T>
where
    State: HasBasic<T> + HasTypeInference<T> + HasSubst<T> + HasQual<T>,
    T: std::fmt::Display + Clone + TypeConstraintInfo<T> + PolyTypeConstraintInfo<T>,
{
    fn solve(&mut self, state: &mut State) {
        match self {
            Constraint::Equality(c) => c.solve(state),
            Constraint::Polymorphism(c) => c.solve(state),
        }
    }
}
