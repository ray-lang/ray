use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::top::{
    TyVar,
    types::{Predicate, Ty},
    util::Join,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeClassDirective<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Never(Predicate<T, V>, I),
    Close(String, I),
    Disjoint(Vec<String>, I),
    Default(String, Vec<T>, I),
}

impl<I, T, V> Display for TypeClassDirective<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeClassDirective::Never(predicate, info) => {
                write!(f, "never {}", predicate)?;
                write!(f, " {{{}}}", info)?;
            }
            TypeClassDirective::Close(name, info) => {
                write!(f, "close {}", name)?;
                write!(f, " {{{}}}", info)?;
            }
            TypeClassDirective::Disjoint(names, info) => {
                write!(f, "disjoint {}", names.join(", "))?;
                write!(f, " {{{}}}", info)?;
            }
            TypeClassDirective::Default(name, types, info) => {
                write!(f, "default {}", name)?;
                write!(f, " {}", types.join(", "))?;
                write!(f, " {{{}}}", info)?;
            }
        }
        Ok(())
    }
}
