mod equality;
mod info;
mod polymorphism;
mod qualifier;

use std::fmt::{Debug, Display};

pub use equality::*;
pub use info::*;
pub use polymorphism::*;
pub use qualifier::*;

use crate::{
    Ty, TyVar,
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{Subst, Substitutable},
};

pub trait Solvable<State, T, V>
where
    Self: Display + Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn solve(&mut self, state: &mut State);

    fn check_condition(&self, _state: &State) -> bool {
        true
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Equality(EqualityConstraint<I, T, V>),
    Polymorphism(PolymorphismConstraint<I, T, V>),
    Qualifier(QualifierConstraint<I, T, V>),
}

impl<I, T, V> Display for Constraint<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Constraint::Equality(c) => write!(f, "{}", c),
            Constraint::Polymorphism(c) => write!(f, "{}", c),
            Constraint::Qualifier(c) => write!(f, "{}", c),
        }
    }
}

impl<I, T, V> From<EqualityConstraint<I, T, V>> for Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn from(c: EqualityConstraint<I, T, V>) -> Self {
        Constraint::Equality(c)
    }
}

impl<I, T, V> From<PolymorphismConstraint<I, T, V>> for Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn from(c: PolymorphismConstraint<I, T, V>) -> Self {
        Constraint::Polymorphism(c)
    }
}

impl<I, T, V> From<QualifierConstraint<I, T, V>> for Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn from(c: QualifierConstraint<I, T, V>) -> Self {
        Constraint::Qualifier(c)
    }
}

impl<I, T, V> Substitutable<V, T> for Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar + Eq,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        match self {
            Constraint::Equality(c) => c.apply_subst(subst),
            Constraint::Polymorphism(c) => c.apply_subst(subst),
            Constraint::Qualifier(c) => c.apply_subst(subst),
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        match self {
            Constraint::Equality(c) => c.apply_subst_all(subst),
            Constraint::Polymorphism(c) => c.apply_subst_all(subst),
            Constraint::Qualifier(c) => c.apply_subst_all(subst),
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Constraint::Equality(c) => c.free_vars(),
            Constraint::Polymorphism(c) => c.free_vars(),
            Constraint::Qualifier(c) => c.free_vars(),
        }
    }
}

impl<State, I, T, V> Solvable<State, T, V> for Constraint<I, T, V>
where
    State: HasBasic<I, T, V> + HasTypeInference<I, T, V> + HasSubst<I, T, V> + HasQual<I, T, V>,
    I: Debug + Display + Clone + TypeConstraintInfo<I, T, V> + PolyTypeConstraintInfo<I, T, V>,
    T: Ty<V>,
    V: TyVar,
{
    fn solve(&mut self, state: &mut State) {
        log::debug!("solve constraint: {}", self);
        match self {
            Constraint::Equality(c) => c.solve(state),
            Constraint::Polymorphism(c) => c.solve(state),
            Constraint::Qualifier(c) => c.solve(state),
        }
    }
}

impl<I, T, V> Constraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn info(&self) -> &I {
        match self {
            Constraint::Equality(c) => &c.info,
            Constraint::Polymorphism(c) => &c.info,
            Constraint::Qualifier(c) => &c.info,
        }
    }

    pub fn info_mut(&mut self) -> &mut I {
        match self {
            Constraint::Equality(c) => &mut c.info,
            Constraint::Polymorphism(c) => &mut c.info,
            Constraint::Qualifier(c) => &mut c.info,
        }
    }
}
