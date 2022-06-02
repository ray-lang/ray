use crate::constraint::{Constraint, PolyTypeConstraintInfo, Solvable, TypeConstraintInfo};

use super::qualification::HasQual;

pub trait HasBasic<T> {
    fn push_constraint(&mut self, constraint: Constraint<T>);
    fn push_constraints(&mut self, constraints: Vec<Constraint<T>>);
    fn pop_constraint(&mut self) -> Option<Constraint<T>>;
    fn discard_constraints(&mut self);

    fn add_labeled_err(&mut self, label: &str, info: T);
    fn get_labeled_errs(&self) -> &Vec<(String, T)>;
    fn update_err_info(&mut self, f: impl FnMut(&mut T));

    fn add_check(&mut self, label: &str, check: bool);
    fn get_checks(&self) -> &Vec<(String, bool)>;

    fn stop_after_first_error(&self) -> bool;
    fn set_stop_after_first_error(&mut self, stop: bool);
    fn check_conditions(&self) -> bool;
    fn set_check_conditions(&mut self, check: bool);
}
