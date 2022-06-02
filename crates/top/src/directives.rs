use crate::{
    types::{Predicate, Ty},
    util::Join,
};

#[derive(Debug)]
pub enum TypeClassDirective<T> {
    Never(Predicate, T),
    Close(String, T),
    Disjoint(Vec<String>, T),
    Default(String, Vec<Ty>, T),
}

impl<T> std::fmt::Display for TypeClassDirective<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeClassDirective::Never(predicate, t) => {
                write!(f, "never {}", predicate)?;
                write!(f, " {}", t)?;
            }
            TypeClassDirective::Close(name, t) => {
                write!(f, "close {}", name)?;
                write!(f, " {}", t)?;
            }
            TypeClassDirective::Disjoint(names, t) => {
                write!(f, "disjoint {}", names.join(", "))?;
                write!(f, " {}", t)?;
            }
            TypeClassDirective::Default(name, types, t) => {
                write!(f, "default {}", name)?;
                write!(f, " {}", types.join(", "))?;
                write!(f, " {}", t)?;
            }
        }
        Ok(())
    }
}
