use crate::{Ty, TyVar, constraint::Constraint};

pub trait HasBasic<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn push_constraint(&mut self, constraint: Constraint<I, T, V>);
    fn push_constraints(&mut self, constraints: Vec<Constraint<I, T, V>>);
    fn pop_constraint(&mut self) -> Option<Constraint<I, T, V>>;
    fn discard_constraints(&mut self);

    fn add_labeled_err(&mut self, label: ErrorLabel, info: I);
    fn get_labeled_errs(&self) -> &Vec<(ErrorLabel, I)>;
    fn update_err_info(&mut self, f: impl FnMut(&mut I));

    fn add_check(&mut self, label: &str, check: bool);
    fn get_checks(&self) -> &Vec<(String, bool)>;

    fn stop_after_first_error(&self) -> bool;
    fn set_stop_after_first_error(&mut self, stop: bool);
    fn check_conditions(&self) -> bool;
    fn set_check_conditions(&mut self, check: bool);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorLabel {
    AmbiguousPredicate,
    MissingPredicate,
    UnsolvedPredicate,
    DisjointPredicates,
    SkolemVersusConstant,
    SkolemVersusSkolem,
    EscapingSkolem,
    RigidTypeVariable,
    Unification,
}
