use std::{
    collections::HashMap,
    iter::FromIterator,
    ops::{Deref, DerefMut, Sub},
};

use serde::{Deserialize, Serialize};

use crate::{
    ast::Path,
    typing::ty::{Ty, TyVar},
    utils::replace,
};

use super::{ApplySubst, Subst};

#[derive(Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyEnv(HashMap<Path, Ty>);

impl std::fmt::Debug for TyEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(s, t)| (s.to_string(), t.to_string())))
            .finish()
    }
}

impl Deref for TyEnv {
    type Target = HashMap<Path, Ty>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TyEnv {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromIterator<(Path, Ty)> for TyEnv {
    fn from_iter<T: IntoIterator<Item = (Path, Ty)>>(iter: T) -> Self {
        TyEnv(iter.into_iter().collect())
    }
}

impl IntoIterator for TyEnv {
    type Item = (Path, Ty);
    type IntoIter = std::collections::hash_map::IntoIter<Path, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, I> Sub<I> for TyEnv
where
    I: Iterator<Item = &'a Path>,
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

impl ApplySubst for TyEnv {
    fn apply_subst(mut self, subst: &Subst) -> Self {
        for (_, ty) in self.iter_mut() {
            replace(ty, |ty| ty.apply_subst(&subst));
        }
        self
    }
}

impl TyEnv {
    pub fn new() -> TyEnv {
        TyEnv(HashMap::new())
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
