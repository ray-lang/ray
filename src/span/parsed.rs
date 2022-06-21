use std::ops::{Deref, DerefMut};

use serde::{Deserialize, Serialize};

use super::{Source, Span};

#[derive(Serialize, Deserialize)]
pub struct Parsed<T> {
    value: T,
    src: Source,
}

impl<T> std::fmt::Debug for Parsed<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.value, f)
    }
}

impl<T> std::fmt::Display for Parsed<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.value, f)
    }
}

impl<T> Clone for Parsed<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            src: self.src.clone(),
        }
    }
}

impl<T> Deref for Parsed<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Parsed<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> PartialEq for Parsed<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<T> Eq for Parsed<T> where T: Eq {}

impl<T> PartialOrd for Parsed<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<T> Ord for Parsed<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<T> std::hash::Hash for Parsed<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<T> Parsed<T> {
    pub fn new(value: T, src: Source) -> Parsed<T> {
        Parsed { value, src }
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn span(&self) -> Option<&Span> {
        self.src.span.as_ref()
    }

    pub fn take(self) -> (T, Source) {
        (self.value, self.src)
    }

    pub fn take_value(self) -> T {
        self.value
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Parsed<U> {
        Parsed {
            value: f(self.value),
            src: self.src,
        }
    }
}

impl<T> Parsed<T>
where
    T: Clone,
{
    pub fn clone_value(&self) -> T {
        self.value.clone()
    }
}
