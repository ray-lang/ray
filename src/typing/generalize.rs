use std::collections::HashMap;

use super::ty::{Ty, TyVar};

pub trait Generalize {
    fn generalize(self, other: Self, reverse_subst: &mut HashMap<(Ty, Ty), TyVar>) -> Self;
}
