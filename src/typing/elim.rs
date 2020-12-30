use std::collections::HashSet;

use crate::typing::ty::TyVar;

use super::InferError;

pub trait Elim {
    fn elim_up<T>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
        T: Copy + Clone;

    fn elim_down<T>(self, vs: &HashSet<&TyVar>) -> Result<Self, InferError<T>>
    where
        Self: Sized,
        T: Copy + Clone;
}
