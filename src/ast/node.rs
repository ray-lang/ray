use std::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use rand::Rng;

use crate::{
    ast::{Decorator, Expr, Path},
    hir::HirInfo,
    pathlib::FilePath,
    span::{Source, SourceMap, Span},
    typing::{traits::HasType, ty::Ty, ApplySubst, Subst, TyCtx},
    utils::replace,
};

pub trait HasSource {
    fn src(&self) -> Source;
    fn set_src(&mut self, src: Source);
    fn span(&self) -> Span {
        self.src().span.unwrap()
    }
}

impl<T> HasSource for Box<T>
where
    T: HasSource,
{
    fn src(&self) -> Source {
        self.as_ref().src()
    }

    fn set_src(&mut self, src: Source) {
        self.as_mut().set_src(src);
    }
}

pub trait HasDoc {
    fn doc(&self) -> Option<String>;
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceInfo {
    pub src: Source,
    pub path: Path,
    pub doc: Option<String>,
}

impl std::fmt::Display for SourceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.src)
    }
}

impl HasSource for SourceInfo {
    fn src(&self) -> Source {
        self.src.clone()
    }

    fn set_src(&mut self, src: Source) {
        self.src = src;
    }
}

impl ApplySubst for SourceInfo {
    fn apply_subst(self, _: &Subst) -> Self {
        self
    }
}

impl SourceInfo {
    pub fn empty() -> SourceInfo {
        SourceInfo {
            src: Source::default(),
            path: Path::new(),
            doc: None,
        }
    }

    pub fn new(src: Source) -> SourceInfo {
        SourceInfo {
            src,
            path: Path::new(),
            doc: None,
        }
    }
}

pub struct Node<T> {
    pub id: u64,
    pub value: T,
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Node<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> std::fmt::Display for Node<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<T> std::fmt::Debug for Node<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("id", &format!("{:x}", self.id))
            .field("value", &self.value)
            .finish()
    }
}

impl<T> Clone for Node<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Node {
            id: self.id.clone(),
            value: self.value.clone(),
        }
    }
}

impl<T> PartialEq for Node<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.value == other.value
    }
}

impl<T> Eq for Node<T> where T: Eq {}

impl<T> PartialOrd for Node<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<T> Ord for Node<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<T> ApplySubst for Node<T>
where
    T: ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> Self {
        Node {
            id: self.id,
            value: self.value.apply_subst(subst),
        }
    }
}

impl<T> Node<T> {
    pub fn new(value: T) -> Node<T> {
        let mut rng = rand::thread_rng();
        let id = rng.gen::<u64>();
        Node { id, value }
    }

    pub fn with_id(id: u64, value: T) -> Node<T> {
        Node { id, value }
    }

    pub fn take_map<F, U>(self, f: F) -> Node<U>
    where
        F: Fn(T) -> U,
    {
        let id = self.id;
        let value = f(self.value);
        Node { id, value }
    }

    pub fn map<F, U>(&self, f: F) -> Node<U>
    where
        F: Fn(&T) -> U,
    {
        let id = self.id;
        let value = f(&self.value);
        Node { id, value }
    }

    pub fn unpack(self) -> (u64, T) {
        (self.id, self.value)
    }
}
