use crate::types::{Subst, Ty};

pub trait HasSubst<T> {
    fn make_subst_consistent(&mut self);

    fn unify_terms(&mut self, info: &T, lhs: &Ty, rhs: &Ty);

    fn get_subst(&self) -> &Subst;

    fn get_subst_mut(&mut self) -> &mut Subst;

    fn find_subst_for_var(&self, var: u32) -> Option<&Ty>;
}
