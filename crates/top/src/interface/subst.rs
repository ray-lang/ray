use crate::{Ty, TyVar, types::Subst};

pub trait HasSubst<I, T, V>
where
    V: TyVar,
{
    fn make_subst_consistent(&mut self);

    fn unify_terms(&mut self, info: &I, lhs: &T, rhs: &T);

    fn get_subst(&self) -> &Subst<V, T>;

    fn get_subst_mut(&mut self) -> &mut Subst<V, T>;

    fn find_subst_for_var(&self, var: &V) -> T;

    fn merge_unifier_subst(&mut self, info: &I, subst: Subst<V, T>);
}
