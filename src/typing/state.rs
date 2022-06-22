use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    iter::FromIterator,
    ops::{Deref, DerefMut, Sub},
};

use serde::{Deserialize, Serialize};
use top::{Subst, Substitutable};

use crate::{
    ast::Path,
    typing::ty::{Ty, TyVar},
};

use super::{
    traits::QualifyTypes,
    ty::{SigmaTy, TyScheme},
};

#[derive(Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Env<T>(HashMap<Path, T>);

pub type TyEnv = Env<Ty>;
pub type SigmaEnv = Env<SigmaTy>;
pub type SchemeEnv = Env<TyScheme>;

impl<T> Debug for Env<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(s, t)| (s.to_string(), t)))
            .finish()
    }
}

impl<T> Display for Env<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            return write!(f, "{{}}");
        }

        write!(f, "{{\n")?;
        for (i, (s, t)) in self.0.iter().enumerate() {
            write!(f, "  {:?}: {:?}", s.to_string(), t.to_string())?;
            if i < self.0.len() - 1 {
                write!(f, ",")?;
            }
            write!(f, "\n")?;
        }
        write!(f, "}}")
    }
}

impl<T> Deref for Env<T> {
    type Target = HashMap<Path, T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Env<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> FromIterator<(Path, T)> for Env<T> {
    fn from_iter<I: IntoIterator<Item = (Path, T)>>(iter: I) -> Self {
        Env(iter.into_iter().collect())
    }
}

impl<T> IntoIterator for Env<T> {
    type Item = (Path, T);
    type IntoIter = std::collections::hash_map::IntoIter<Path, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Into<Env<SigmaTy>> for Env<TyScheme> {
    fn into(self) -> Env<SigmaTy> {
        let mut env = Env::new();
        for (path, scheme) in self {
            env.insert(path, SigmaTy::scheme(scheme));
        }
        env
    }
}

impl<'a, I, T> Sub<I> for Env<T>
where
    I: Iterator<Item = &'a Path>,
{
    type Output = Env<T>;

    fn sub(self, rhs: I) -> Self::Output {
        let mut env = self;
        for k in rhs {
            env.remove(k);
        }
        env
    }
}

impl<T> Substitutable<TyVar, T> for Env<T>
where
    T: Clone + Substitutable<TyVar, T>,
{
    fn apply_subst(&mut self, subst: &Subst<TyVar, T>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, T>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        self.iter().flat_map(|(_, ty)| ty.free_vars()).collect()
    }
}

impl Substitutable<TyVar, Ty> for Env<SigmaTy> {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        self.iter().flat_map(|(_, ty)| ty.free_vars()).collect()
    }
}

impl Substitutable<TyVar, Ty> for Env<TyScheme> {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        self.iter().flat_map(|(_, ty)| ty.free_vars()).collect()
    }
}

impl<T> QualifyTypes for Env<T>
where
    T: QualifyTypes,
{
    fn qualify_tys(&mut self, preds: &Vec<top::Predicate<Ty, TyVar>>) {
        for (_, ty) in self.iter_mut() {
            ty.qualify_tys(preds);
        }
    }
}

impl<T> Env<T> {
    pub fn new() -> Self {
        Env(HashMap::new())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyVarFactory {
    value: u64,
    prefix: String,
    scope: Option<Path>,
}

impl<'a> From<&'a TyVarFactory> for TyVarFactory {
    fn from(tf: &'a TyVarFactory) -> Self {
        Self {
            value: tf.value,
            prefix: tf.prefix.clone(),
            scope: tf.scope.clone(),
        }
    }
}

impl TyVarFactory {
    pub fn new(prefix: &'static str) -> TyVarFactory {
        TyVarFactory {
            value: 0,
            scope: None,
            prefix: prefix.to_string(),
        }
    }

    pub fn scoped(prefix: &'static str, scope: Path) -> TyVarFactory {
        TyVarFactory {
            value: 0,
            scope: Some(scope),
            prefix: prefix.to_string(),
        }
    }

    pub fn set_prefix<S: AsRef<str>>(&mut self, prefix: S) {
        self.prefix = prefix.as_ref().to_string();
    }

    pub fn curr(&self) -> u64 {
        self.value
    }

    pub fn skip_to(&mut self, value: u64) {
        self.value = value;
    }

    pub fn next(&mut self) -> TyVar {
        let v = self.value;
        self.value += 1;
        // if v == 46 {
        //     panic!("v = 46")
        // }
        let name = format!("{}{}", self.prefix, v);
        if let Some(scope) = &self.scope {
            let path = scope.append(name);
            TyVar(path)
        } else {
            TyVar::from(name)
        }
    }

    pub fn with_scope(&mut self, scope: &Path) -> TyVar {
        let v = self.value;
        self.value += 1;
        // if v == 46 {
        //     panic!("v = 46")
        // }
        // let path = scope.append(format!("{}{}", self.prefix, v));
        let path = Path::from(format!("{}{}", self.prefix, v));
        TyVar(path)
    }
}
