use std::{fmt::Debug, ops::Deref};

use rand::Rng;

use crate::{
    ast::Expr,
    span::Source,
    typing::{traits::HasType, ty::Ty, ApplySubst, Subst},
};

pub trait HasExpr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn expr(&self) -> &Expr<Info>;
    fn take_expr(self) -> Expr<Info>;
}

pub trait HasSource {
    fn src(&self) -> Source;
    fn set_src(&mut self, src: Source);
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

pub type SourceNode<T> = Node<T, SourceInfo>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceInfo {
    pub src: Source,
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
    pub fn new(src: Source) -> SourceInfo {
        SourceInfo { src, doc: None }
    }
}

#[derive(Eq)]
pub struct Node<T, U> {
    pub id: u64,
    pub value: T,
    pub info: U,
}

impl<T, U> Deref for Node<T, U> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T, U> std::fmt::Display for Node<T, U>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<T, U> std::fmt::Debug for Node<T, U>
where
    T: std::fmt::Debug,
    U: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("id", &format!("{:x}", self.id))
            .field("value", &self.value)
            .field("info", &self.info)
            .finish()
    }
}

impl<T, U> Clone for Node<T, U>
where
    T: Clone,
    U: Clone,
{
    fn clone(&self) -> Self {
        Node {
            id: self.id.clone(),
            value: self.value.clone(),
            info: self.info.clone(),
        }
    }
}

impl<T, U> PartialEq for Node<T, U>
where
    T: PartialEq,
    U: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.value == other.value && self.info == other.info
    }
}

impl<Info> HasExpr<Info> for Node<Expr<Info>, Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn expr(&self) -> &Expr<Info> {
        &self.value
    }

    fn take_expr(self) -> Expr<Info> {
        self.value
    }
}

impl<T, Info> HasSource for Node<T, Info>
where
    Info: HasSource,
{
    fn src(&self) -> Source {
        self.info.src()
    }

    fn set_src(&mut self, src: Source) {
        self.info.set_src(src);
    }
}

impl<T, Info> HasType for Node<T, Info>
where
    Info: HasType,
{
    fn ty(&self) -> Ty {
        self.info.ty()
    }
}

impl<T, U> ApplySubst for Node<T, U>
where
    T: ApplySubst,
    U: ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> Self {
        Node {
            id: self.id,
            value: self.value.apply_subst(subst),
            info: self.info.apply_subst(subst),
        }
    }
}

impl<T, U> Node<T, U> {
    pub fn new(value: T, info: U) -> Node<T, U> {
        let mut rng = rand::thread_rng();
        let id = rng.gen::<u64>();
        Node { id, value, info }
    }

    pub fn unpack(self) -> (u64, T, U) {
        (self.id, self.value, self.info)
    }
}
