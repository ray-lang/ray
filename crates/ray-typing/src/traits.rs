use crate::top::Predicate;

use super::{
    constraints::Constraint,
    ty::{Ty, TyScheme, TyVar},
};

pub trait QualifyTypes {
    fn qualify_tys(&mut self, preds: &Vec<Predicate<Ty, TyVar>>);
}

impl<'a> QualifyTypes for std::vec::IntoIter<&'a mut TyScheme> {
    fn qualify_tys(&mut self, preds: &Vec<Predicate<Ty, TyVar>>) {
        for t in self {
            t.qualify_tys(preds);
        }
    }
}

impl<'a, K> QualifyTypes for std::collections::hash_map::ValuesMut<'a, K, TyScheme> {
    fn qualify_tys(&mut self, preds: &Vec<Predicate<Ty, TyVar>>) {
        for t in self {
            t.qualify_tys(preds);
        }
    }
}

impl<'a, T> QualifyTypes for Vec<T>
where
    T: QualifyTypes,
{
    fn qualify_tys(&mut self, preds: &Vec<Predicate<Ty, TyVar>>) {
        for t in self.iter_mut() {
            t.qualify_tys(preds);
        }
    }
}

pub trait TreeWalk: Copy {
    fn walk(
        self,
        down: Vec<Constraint>,
        pairs: Vec<(Vec<Constraint>, Vec<Constraint>)>,
    ) -> Vec<Constraint>;
}
