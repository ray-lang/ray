use std::ops::{Deref, DerefMut};

use crate::typing::ty::Ty;

pub struct Typed<T> {
    value: T,
    ty: Option<Ty>,
}

impl<T> std::fmt::Debug for Typed<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(t) = &self.ty {
            write!(f, "{:?}: {:?}", self.value, t)
        } else {
            write!(f, "{:?}", self.value)
        }
    }
}

impl<T> std::fmt::Display for Typed<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(t) = &self.ty {
            write!(f, "{}: {}", self.value, t)
        } else {
            write!(f, "{}", self.value)
        }
    }
}

impl<T> Clone for Typed<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            ty: self.ty.clone(),
        }
    }
}

impl<T> Deref for Typed<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Typed<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> PartialEq for Typed<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<T> Eq for Typed<T> where T: Eq {}

impl<T> PartialOrd for Typed<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<T> Ord for Typed<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<T> std::hash::Hash for Typed<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<T> Typed<T> {
    pub fn new(value: T, ty: Option<Ty>) -> Typed<T> {
        Typed { value, ty }
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn ty(&self) -> Option<&Ty> {
        self.ty.as_ref()
    }

    pub fn take(self) -> (T, Option<Ty>) {
        (self.value, self.ty)
    }

    pub fn take_value(self) -> T {
        self.value
    }
}

impl<T> Typed<T>
where
    T: Clone,
{
    pub fn clone_value(&self) -> T {
        self.value.clone()
    }
}
