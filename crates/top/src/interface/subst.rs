use crate::{types::Subst, TyVar};

pub trait HasSubst<I, T, V>
where
    V: TyVar,
{
    fn make_subst_consistent(&mut self);

    fn unify_terms(&mut self, info: &I, lhs: &T, rhs: &T);

    fn get_subst(&self) -> &Subst<V, T>;

    fn get_subst_mut(&mut self) -> &mut Subst<V, T>;

    fn find_subst_for_var(&self, var: &V) -> T;
}
