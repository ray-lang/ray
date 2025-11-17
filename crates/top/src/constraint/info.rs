use crate::{
    Predicates, TyVar,
    types::{Predicate, Scheme, Ty},
};

pub trait InfoJoin {
    fn join(self, other: Self) -> Self;
}

pub trait InfoDetail {
    fn add_detail(&mut self, detail: &str);
}

pub trait TypeConstraintInfo<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn equality_type_pair(&mut self, lhs: &T, rhs: &T);

    fn missing_predicate(&mut self, predicate: &Predicate<T, V>);

    fn ambiguous_predicate(&mut self, predicate: &Predicate<T, V>);

    fn unsolved_predicate(&mut self, predicate: &Predicate<T, V>, info: &I);

    fn predicate_arising_from(&mut self, predicate: &Predicate<T, V>);

    fn parent_predicate(&mut self, predicate: &Predicate<T, V>);

    fn escaped_skolems(&mut self, skolems: &[V]);

    fn never_directive(&mut self, predicate: &Predicate<T, V>, info: &I);

    fn close_directive(&mut self, name: &String, info: &I);

    fn disjoint_directive(&mut self, lhs: &String, lhs_info: &I, rhs: &String, rhs_info: &I);
}

pub trait PolyTypeConstraintInfo<I, T, V>: TypeConstraintInfo<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn instantiated_type_scheme(&mut self, scheme: &Scheme<Predicates<T, V>, T, V>);

    fn skolemized_type_scheme(&mut self, tys: &Vec<T>, scheme: &Scheme<Predicates<T, V>, T, V>);
}
