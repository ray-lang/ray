use std::fmt::{Debug, Display};

use crate::{
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{Predicate, Subst, Substitutable, Ty},
    TyVar,
};

use super::{PolyTypeConstraintInfo, Solvable};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QualConstraintKind<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Prove(Predicate<T, V>),
    Assume(Predicate<T, V>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QualifierConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) kind: QualConstraintKind<T, V>,
    pub(crate) info: I,
}

impl<I, T, V> Display for QualifierConstraint<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            QualConstraintKind::Prove(pred) => write!(f, "Prove({})", pred),
            QualConstraintKind::Assume(pred) => write!(f, "Assume({})", pred),
        }?;

        write!(f, " : {{{}}}", self.info)
    }
}

impl<I, T, V> Substitutable<V, T> for QualifierConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        match &mut self.kind {
            QualConstraintKind::Prove(pred) => pred.apply_subst(subst),
            QualConstraintKind::Assume(pred) => pred.apply_subst(subst),
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match &self.kind {
            QualConstraintKind::Prove(pred) => pred.free_vars(),
            QualConstraintKind::Assume(pred) => pred.free_vars(),
        }
    }
}

impl<State, I, T, V> Solvable<State, T, V> for QualifierConstraint<I, T, V>
where
    State: HasBasic<I, T, V> + HasTypeInference<I, T, V> + HasSubst<I, T, V> + HasQual<I, T, V>,
    I: Display + Clone + PolyTypeConstraintInfo<I, T, V>,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn solve(&mut self, state: &mut State) {
        match &self.kind {
            QualConstraintKind::Prove(qualifier) => {
                state.prove_qualifier(qualifier.clone(), &self.info)
            }
            QualConstraintKind::Assume(qualifier) => {
                state.assume_qualifier(qualifier.clone(), &self.info)
            }
        }
    }
}

impl<I, T, V> QualifierConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn prove(pred: Predicate<T, V>, info: I) -> Self {
        QualifierConstraint {
            kind: QualConstraintKind::Prove(pred),
            info,
        }
    }

    pub fn assume(pred: Predicate<T, V>, info: I) -> Self {
        QualifierConstraint {
            kind: QualConstraintKind::Assume(pred),
            info,
        }
    }
}
