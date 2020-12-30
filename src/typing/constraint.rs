use std::collections::{
    hash_map::{IntoIter as HashMapIntoIter, Iter as HashMapIter},
    HashMap,
};

use super::{
    bound::{GreatestLowerBound, LeastUpperBound},
    subst::Subst,
    ty::{Ty, TyVar},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstraintSet {
    constraints: HashMap<TyVar, Constraint>,
}

impl IntoIterator for ConstraintSet {
    type Item = (TyVar, Constraint);
    type IntoIter = HashMapIntoIter<TyVar, Constraint>;

    fn into_iter(self) -> Self::IntoIter {
        self.constraints.into_iter()
    }
}

impl ConstraintSet {
    pub fn new() -> ConstraintSet {
        ConstraintSet {
            constraints: HashMap::new(),
        }
    }

    pub fn add(&mut self, tv: TyVar, c: Constraint) {
        self.constraints.insert(tv, c);
    }

    pub fn to_subst(&self) -> Subst {
        // creates a substitution using the constraints
        let mut sub = Subst::new();
        for (tv, c) in self.iter() {
            if let Constraint::Subtype(x, _, y) = c {
                let t = if matches!(x, Ty::Never) {
                    y.clone()
                } else {
                    x.clone()
                };
                sub.insert(tv.clone(), t);
            }
        }
        sub
    }

    /// C ∧ D: The meet of two X/V -constraint sets C and D
    /// { (S ∨ U) <: X[i] <: (T ∧ V) | (S <: X[i] <: T) ∈ C and (U <: X[i] <: V) ∈ D}
    pub fn meet(self, mut other: ConstraintSet) -> ConstraintSet {
        let mut new_set = ConstraintSet::new();
        for (tv, c) in self.constraints.into_iter() {
            if let Some(d) = other.constraints.remove(&tv) {
                let (s, _, t) = c.unpack();
                let (u, _, v) = d.unpack();
                let x = s.least_upper_bound(&u);
                let y = t.greatest_lower_bound(&v);
                new_set
                    .constraints
                    .insert(tv.clone(), Constraint::Subtype(x, Ty::Var(tv), y));
            } else {
                new_set.constraints.insert(tv, c);
            }
        }

        for (tv, d) in other.constraints.into_iter() {
            new_set.constraints.insert(tv, d);
        }

        new_set
    }

    pub fn iter(&self) -> HashMapIter<'_, TyVar, Constraint> {
        self.constraints.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Constraint {
    Eq(Ty, Ty),
    Subtype(Ty, Ty, Ty),
}

impl Constraint {
    pub fn unpack(self) -> (Ty, Ty, Ty) {
        match self {
            Constraint::Subtype(s, x, t) => (s, x, t),
            _ => unreachable!(),
        }
    }
}
