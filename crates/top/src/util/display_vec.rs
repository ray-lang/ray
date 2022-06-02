use std::ops::{Deref, DerefMut};

use crate::types::{ShowQualifiers, Subst, Substitutable};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DisplayableVec<T>(Vec<T>)
where
    T: std::fmt::Display;

impl<T> Deref for DisplayableVec<T>
where
    T: std::fmt::Display,
{
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for DisplayableVec<T>
where
    T: std::fmt::Display,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> std::fmt::Display for DisplayableVec<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, x) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", x)?;
        }

        write!(f, "]")
    }
}

impl<T> Into<Vec<T>> for DisplayableVec<T>
where
    T: std::fmt::Display,
{
    fn into(self) -> Vec<T> {
        self.0
    }
}

impl<T> From<Vec<T>> for DisplayableVec<T>
where
    T: std::fmt::Display,
{
    fn from(t: Vec<T>) -> Self {
        Self(t)
    }
}

impl<T> Substitutable for DisplayableVec<T>
where
    T: std::fmt::Display + Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        for x in &mut self.0 {
            x.apply_subst(subst);
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        self.0.iter().flat_map(|x| x.free_vars()).collect()
    }
}

impl<T> ShowQualifiers for DisplayableVec<T>
where
    T: std::fmt::Display + ShowQualifiers,
{
    fn show_qualifiers(&self) -> Vec<String> {
        self.0.show_qualifiers()
    }
}
