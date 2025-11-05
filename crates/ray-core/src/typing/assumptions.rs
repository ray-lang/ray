use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
    ops::{Deref, DerefMut, Sub},
};

use crate::{ast::Path, typing::ty::Ty};

#[derive(Clone, PartialEq, Eq)]
pub struct AssumptionSet {
    map: HashMap<Path, HashSet<Ty>>,
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
    type Target = HashMap<Path, HashSet<Ty>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for AssumptionSet {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl FromIterator<(Path, Ty)> for AssumptionSet {
    fn from_iter<T: IntoIterator<Item = (Path, Ty)>>(iter: T) -> Self {
        let mut aset = AssumptionSet::new();
        for (path, ty) in iter {
            aset.add(path, ty);
        }
        aset
    }
}

impl IntoIterator for AssumptionSet {
    type Item = (Path, HashSet<Ty>);
    type IntoIter = std::collections::hash_map::IntoIter<Path, HashSet<Ty>>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl Extend<(Path, Vec<Ty>)> for AssumptionSet {
    fn extend<T: IntoIterator<Item = (Path, Vec<Ty>)>>(&mut self, iter: T) {
        for (path, tys) in iter {
            for ty in tys {
                self.add(path.clone(), ty);
            }
        }
    }
}

impl Extend<(Path, HashSet<Ty>)> for AssumptionSet {
    fn extend<T: IntoIterator<Item = (Path, HashSet<Ty>)>>(&mut self, iter: T) {
        for (path, tys) in iter {
            for ty in tys {
                self.add(path.clone(), ty);
            }
        }
    }
}

impl Extend<(Path, Ty)> for AssumptionSet {
    fn extend<T: IntoIterator<Item = (Path, Ty)>>(&mut self, iter: T) {
        for (path, ty) in iter {
            self.add(path, ty);
        }
    }
}

impl From<Vec<(Path, Ty)>> for AssumptionSet {
    fn from(v: Vec<(Path, Ty)>) -> AssumptionSet {
        let mut aset = AssumptionSet::new();
        for (path, t) in v {
            aset.add(path, t);
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
    I: Iterator<Item = &'a Path>,
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

// impl ApplySubst for AssumptionSet {
//     fn apply_subst(self, subst: &Subst) -> Self {
//         let mut aset = Self::new();
//         for (path, tys) in self {
//             aset.insert(
//                 path,
//                 tys.into_iter().map(|t| t.apply_subst(subst)).collect(),
//             );
//         }
//         aset
//     }
// }

// impl CollectTyVars for AssumptionSet {
//     fn collect_tyvars(&self) -> Vec<TyVar> {
//         self.iter()
//             .flat_map(|(_, tys)| tys.iter().map(|ty| ty.collect_tyvars()))
//             .flatten()
//             .collect()
//     }
// }

impl AssumptionSet {
    pub fn new() -> AssumptionSet {
        AssumptionSet {
            map: HashMap::new(),
        }
    }

    pub fn add(&mut self, path: Path, ty: Ty) {
        if let Some(v) = self.map.get_mut(&path) {
            v.insert(ty);
        } else {
            self.map.insert(path, vec![ty].into_iter().collect());
        }
    }
}
