use std::{
    collections::HashMap,
    iter::FromIterator,
    ops::{Deref, DerefMut, Sub},
};

use crate::typing::ty::{Ty, TyVar};

#[derive(Clone, PartialEq, Eq)]
pub struct TyEnv(HashMap<String, Ty>);

impl std::fmt::Debug for TyEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(s, t)| (s, t.to_string())))
            .finish()
    }
}

impl Deref for TyEnv {
    type Target = HashMap<String, Ty>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TyEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromIterator<(String, Ty)> for TyEnv {
    fn from_iter<T: IntoIterator<Item = (String, Ty)>>(iter: T) -> Self {
        TyEnv(iter.into_iter().collect())
    }
}

impl IntoIterator for TyEnv {
    type Item = (String, Ty);
    type IntoIter = std::collections::hash_map::IntoIter<String, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, I> Sub<I> for TyEnv
where
    I: Iterator<Item = &'a String>,
{
    type Output = TyEnv;

    fn sub(self, rhs: I) -> TyEnv {
        let mut env = self;
        for k in rhs {
            env.remove(k);
        }
        env
    }
}

impl TyEnv {
    pub fn new() -> TyEnv {
        TyEnv(HashMap::new())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TyVarFactory {
    value: u64,
    prefix: &'static str,
}

impl TyVarFactory {
    pub fn new(prefix: &'static str) -> TyVarFactory {
        TyVarFactory { value: 0, prefix }
    }

    pub fn skip_to(&mut self, value: u64) {
        self.value = value;
    }

    pub fn next(&mut self) -> TyVar {
        let v = self.value;
        self.value += 1;
        TyVar(format!("{}{}", self.prefix, v))
    }
}
