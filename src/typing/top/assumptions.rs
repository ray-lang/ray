use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut, Sub},
};

use crate::typing::ty::Ty;

#[derive(Clone, PartialEq, Eq)]
pub struct AssumptionSet {
    map: HashMap<String, HashSet<Ty>>,
}

impl std::fmt::Debug for AssumptionSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let entries = self
            .map
            .iter()
            .map(|(s, tys)| (s, tys.iter().map(|t| t.to_string()).collect::<Vec<_>>()));
        f.debug_map().entries(entries).finish()
    }
}

impl Deref for AssumptionSet {
    type Target = HashMap<String, HashSet<Ty>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for AssumptionSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl IntoIterator for AssumptionSet {
    type Item = (String, HashSet<Ty>);
    type IntoIter = std::collections::hash_map::IntoIter<String, HashSet<Ty>>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl From<Vec<(String, Ty)>> for AssumptionSet {
    fn from(v: Vec<(String, Ty)>) -> AssumptionSet {
        let mut aset = AssumptionSet::new();
        for (x, t) in v {
            aset.add(x, t);
        }
        aset
    }
}

impl From<Vec<AssumptionSet>> for AssumptionSet {
    fn from(v: Vec<AssumptionSet>) -> AssumptionSet {
        let mut aset = AssumptionSet::new();
        for a in v {
            aset.extend(a);
        }
        aset
    }
}

impl<'a, I> Sub<I> for AssumptionSet
where
    I: Iterator<Item = &'a String>,
{
    type Output = AssumptionSet;

    fn sub(self, rhs: I) -> AssumptionSet {
        let mut aset = self;
        for k in rhs {
            aset.remove(k);
        }
        aset
    }
}

impl AssumptionSet {
    pub fn new() -> AssumptionSet {
        AssumptionSet {
            map: HashMap::new(),
        }
    }

    pub fn add(&mut self, x: String, ty: Ty) {
        if let Some(v) = self.map.get_mut(&x) {
            v.insert(ty);
        } else {
            self.map.insert(x, vec![ty].into_iter().collect());
        }
    }

    pub fn extend(&mut self, other: AssumptionSet) {
        for (x, tys) in other {
            for ty in tys {
                self.add(x.clone(), ty);
            }
        }
    }
}
