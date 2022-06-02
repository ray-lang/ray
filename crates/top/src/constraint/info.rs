use crate::types::{Predicate, Scheme, Ty};

pub trait InfoDetail {
    fn add_detail(&mut self, detail: &str);
}

pub trait TypeConstraintInfo<T> {
    fn equality_type_pair(&mut self, lhs: &Ty, rhs: &Ty);

    fn ambiguous_predicate(&mut self, predicate: &Predicate);

    fn unsolved_predicate(&mut self, predicate: &Predicate, info: &T);

    fn predicate_arising_from(&mut self, predicate: &Predicate);

    fn parent_predicate(&mut self, predicate: &Predicate);

    fn escaped_skolems(&mut self, skolems: &[u32]);

    fn never_directive(&mut self, predicate: &Predicate, info: &T);

    fn close_directive(&mut self, directive: &String, info: &T);

    fn disjoint_directive(&mut self, lhs: &String, lhs_info: &T, rhs: &String, rhs_info: &T);
}

pub trait PolyTypeConstraintInfo<T>: TypeConstraintInfo<T> {
    fn instantiated_type_scheme(&mut self, scheme: &Scheme<Vec<Predicate>>);

    fn skolemized_type_scheme(&mut self, tys: &Vec<Ty>, scheme: &Scheme<Vec<Predicate>>);
}
