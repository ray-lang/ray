use std::fmt::Debug;

use ray_shared::{pathlib::Path, span::parsed::Parsed};
use serde::{Deserialize, Serialize};

use crate::ast::{Boxed, Node, Ref, expr::deref::Deref};
use ray_typing::types::TyScheme;

use super::{
    Assign, BinOp, Block, BuiltinCall, Call, Cast, Closure, Curly, Dict, Dot, FString, For, Func,
    If, Index, List, Literal, Loop, Missing, Name, New, NilCoalesce, Pattern, Range, ScopedAccess,
    Sequence, Set, Tuple, UnaryOp, While,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expr {
    Assign(Assign),
    BinOp(BinOp),
    Block(Block),
    Boxed(Boxed),
    Break(Option<Box<Node<Expr>>>),
    BuiltinCall(BuiltinCall),
    Continue,
    Call(Call),
    Cast(Cast),
    Closure(Closure),
    Curly(Curly),
    Dict(Dict),
    DefaultValue(Box<Node<Expr>>),
    Deref(Deref),
    Dot(Dot),
    FString(FString),
    Func(Func),
    For(For),
    If(If),
    Index(Index),
    Labeled(Box<Node<Expr>>, Box<Node<Expr>>),
    List(List),
    Literal(Literal),
    Loop(Loop),
    Missing(Missing),
    Name(Name),
    New(New),
    NilCoalesce(NilCoalesce),
    /// A qualified path like `std::collections::HashMap`.
    /// Each segment is a Node with its own NodeId for name resolution.
    Path(Vec<Node<String>>),
    Pattern(Pattern),
    Paren(Box<Node<Expr>>),
    Range(Range),
    Ref(Ref),
    Return(Option<Box<Node<Expr>>>),
    Sequence(Sequence),
    Set(Set),
    ScopedAccess(ScopedAccess),
    Some(Box<Node<Expr>>),
    Tuple(Tuple),
    Type(Parsed<TyScheme>),
    TypeAnnotated(Box<Node<Expr>>, Node<Parsed<TyScheme>>),
    UnaryOp(UnaryOp),
    Unsafe(Box<Node<Expr>>),
    While(While),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum ValueKind {
    LValue,
    RValue,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum TrailingPolicy {
    Allow,
    Forbid,
    Warn,
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Expr::Assign(ex) => ex.to_string(),
                Expr::BinOp(ex) => ex.to_string(),
                Expr::Block(ex) => ex.to_string(),
                Expr::Boxed(ex) => ex.to_string(),
                Expr::Break(ex) => ex.as_ref().map_or_else(
                    || "(break)".to_string(),
                    |ex| format!("(break {})", ex.to_string())
                ),
                Expr::BuiltinCall(ex) => ex.to_string(),
                Expr::Continue => "(continue)".to_string(),
                Expr::Call(ex) => ex.to_string(),
                Expr::Cast(ex) => ex.to_string(),
                Expr::Closure(ex) => ex.to_string(),
                Expr::Curly(ex) => ex.to_string(),
                Expr::Dict(ex) => ex.to_string(),
                Expr::DefaultValue(ex) => ex.to_string(),
                Expr::Deref(ex) => ex.to_string(),
                Expr::Dot(ex) => ex.to_string(),
                Expr::FString(ex) => ex.to_string(),
                Expr::Func(ex) => ex.to_string(),
                Expr::For(ex) => ex.to_string(),
                Expr::If(ex) => ex.to_string(),
                Expr::Index(ex) => ex.to_string(),
                Expr::Labeled(label, ex) => format!("({}: {})", label, ex),
                Expr::List(ex) => ex.to_string(),
                Expr::Literal(ex) => ex.to_string(),
                Expr::Loop(ex) => ex.to_string(),
                Expr::Missing(ex) => ex.to_string(),
                Expr::Name(ex) => ex.to_string(),
                Expr::New(ex) => ex.to_string(),
                Expr::NilCoalesce(ex) => ex.to_string(),
                Expr::Path(segments) => segments
                    .iter()
                    .map(|s| s.value.as_str())
                    .collect::<Vec<_>>()
                    .join("::"),
                Expr::Pattern(ex) => ex.to_string(),
                Expr::Paren(ex) => ex.to_string(),
                Expr::Range(ex) => ex.to_string(),
                Expr::Ref(ex) => ex.to_string(),
                Expr::Return(ex) => ex
                    .as_ref()
                    .map_or_else(|| "(return)".to_string(), |ex| format!("(return {})", ex)),
                Expr::Sequence(ex) => ex.to_string(),
                Expr::Set(ex) => ex.to_string(),
                Expr::ScopedAccess(ex) => ex.to_string(),
                Expr::Some(ex) => format!("(some {})", ex),
                Expr::Tuple(ex) => ex.to_string(),
                Expr::Type(ex) => ex.to_string(),
                Expr::TypeAnnotated(value, ty) => format!("({} :: {})", value, ty),
                Expr::UnaryOp(ex) => ex.to_string(),
                Expr::Unsafe(ex) => format!("(unsafe {})", ex),
                Expr::While(ex) => ex.to_string(),
            }
        )
    }
}

impl Expr {
    pub fn kind(&self) -> &'static str {
        match self {
            Expr::Assign(..) => "Assign",
            Expr::BinOp(..) => "BinOp",
            Expr::Block(..) => "Block",
            Expr::Boxed(..) => "Boxed",
            Expr::Break(..) => "Break",
            Expr::BuiltinCall(..) => "BuiltinCall",
            Expr::Continue => "Continue",
            Expr::Call(..) => "Call",
            Expr::Cast(..) => "Cast",
            Expr::Closure(..) => "Closure",
            Expr::Curly(..) => "Curly",
            Expr::Dict(..) => "Dict",
            Expr::DefaultValue(..) => "DefaultValue",
            Expr::Deref(..) => "Deref",
            Expr::Dot(..) => "Dot",
            Expr::FString(..) => "FString",
            Expr::Func(..) => "Func",
            Expr::For(..) => "For",
            Expr::If(..) => "If",
            Expr::Index(..) => "Index",
            Expr::Labeled(..) => "Labeled",
            Expr::List(..) => "List",
            Expr::Literal(..) => "Literal",
            Expr::Loop(..) => "Loop",
            Expr::Missing(..) => "Missing",
            Expr::Name(..) => "Name",
            Expr::New(..) => "New",
            Expr::NilCoalesce(..) => "NilCoalesce",
            Expr::Path(..) => "Path",
            Expr::Pattern(..) => "Pattern",
            Expr::Paren(..) => "Paren",
            Expr::Range(..) => "Range",
            Expr::Ref(..) => "Ref",
            Expr::Return(..) => "Return",
            Expr::Sequence(..) => "Sequence",
            Expr::Set(..) => "Set",
            Expr::ScopedAccess(..) => "ScopedAccess",
            Expr::Some(..) => "Some",
            Expr::Tuple(..) => "Tuple",
            Expr::Type(..) => "Type",
            Expr::TypeAnnotated(..) => "TypeAnnotated",
            Expr::UnaryOp(..) => "UnaryOp",
            Expr::Unsafe(..) => "Unsafe",
            Expr::While(..) => "While",
        }
    }

    pub fn path(&self) -> Option<&Path> {
        match self {
            Expr::Name(n) => Some(&n.path),
            Expr::Func(f) => Some(&f.sig.path.value),
            Expr::Pattern(p) => p.path(),
            Expr::Assign(_)
            | Expr::Path(_)
            | Expr::BinOp(_)
            | Expr::Block(_)
            | Expr::Boxed(_)
            | Expr::Break(_)
            | Expr::BuiltinCall(_)
            | Expr::Continue
            | Expr::Call(_)
            | Expr::Cast(_)
            | Expr::Closure(_)
            | Expr::Curly(_)
            | Expr::Dict(_)
            | Expr::DefaultValue(_)
            | Expr::Deref(_)
            | Expr::Dot(_)
            | Expr::For(_)
            | Expr::FString(_)
            | Expr::If(_)
            | Expr::Index(_)
            | Expr::Labeled(_, _)
            | Expr::Literal(_)
            | Expr::List(_)
            | Expr::Loop(_)
            | Expr::Missing(_)
            | Expr::New(_)
            | Expr::NilCoalesce(_)
            | Expr::Paren(_)
            | Expr::Range(_)
            | Expr::Ref(_)
            | Expr::Return(_)
            | Expr::Sequence(_)
            | Expr::Set(_)
            | Expr::ScopedAccess(_)
            | Expr::Some(_)
            | Expr::Tuple(_)
            | Expr::Type(_)
            | Expr::TypeAnnotated(..)
            | Expr::UnaryOp(_)
            | Expr::Unsafe(_)
            | Expr::While(_) => None,
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Expr::Name(n) => Some(n.path.to_string()),
            Expr::Func(f) => f.sig.path.name(),
            Expr::Pattern(p) => p.get_name(),
            Expr::Path(segments) => Some(
                segments
                    .iter()
                    .map(|s| s.value.as_str())
                    .collect::<Vec<_>>()
                    .join("::"),
            ),
            Expr::Assign(_)
            | Expr::BinOp(_)
            | Expr::Block(_)
            | Expr::Boxed(_)
            | Expr::Break(_)
            | Expr::BuiltinCall(_)
            | Expr::Continue
            | Expr::Call(_)
            | Expr::Cast(_)
            | Expr::Closure(_)
            | Expr::Curly(_)
            | Expr::Dict(_)
            | Expr::DefaultValue(_)
            | Expr::Deref(_)
            | Expr::Dot(_)
            | Expr::For(_)
            | Expr::FString(_)
            | Expr::If(_)
            | Expr::Index(_)
            | Expr::Labeled(_, _)
            | Expr::Literal(_)
            | Expr::List(_)
            | Expr::Loop(_)
            | Expr::Missing(_)
            | Expr::New(_)
            | Expr::NilCoalesce(_)
            | Expr::Paren(_)
            | Expr::Range(_)
            | Expr::Ref(_)
            | Expr::Return(_)
            | Expr::Sequence(_)
            | Expr::Set(_)
            | Expr::ScopedAccess(_)
            | Expr::Some(_)
            | Expr::Tuple(_)
            | Expr::Type(_)
            | Expr::TypeAnnotated(..)
            | Expr::UnaryOp(_)
            | Expr::Unsafe(_)
            | Expr::While(_) => None,
        }
    }

    pub fn desc(&self) -> &'static str {
        match self {
            Expr::List(..) => "array",
            Expr::Assign(..) => "assign",
            Expr::BinOp(..) => "binary operation",
            Expr::Block(..) => "block",
            Expr::Boxed(..) => "box",
            Expr::Break(..) => "break",
            Expr::BuiltinCall(..) => "builtin call",
            Expr::Continue => "continue",
            Expr::Call(..) => "call",
            Expr::Cast(..) => "cast",
            Expr::Closure(..) => "closure",
            Expr::Curly(..) => "curly",
            Expr::Dict(..) => "dict",
            Expr::DefaultValue(..) => "default value",
            Expr::Deref(..) => "deref",
            Expr::Dot(..) => "dot",
            Expr::FString(..) => "f-string",
            Expr::Func(..) => "function",
            Expr::For(..) => "for",
            Expr::If(..) => "if",
            Expr::Index(..) => "index",
            Expr::Labeled(..) => "labeled",
            Expr::Literal(..) => "literal",
            Expr::Loop(..) => "loop",
            Expr::Missing(..) => "missing expression",
            Expr::Name(..) => "name",
            Expr::New(..) => "new",
            Expr::NilCoalesce(..) => "nil coalesce",
            Expr::Pattern(..) => "pattern",
            Expr::Path(..) => "path",
            Expr::Paren(..) => "paren",
            Expr::Range(..) => "range",
            Expr::Ref(..) => "ref",
            Expr::Return(..) => "return",
            Expr::Sequence(..) => "sequence",
            Expr::Set(..) => "set",
            Expr::ScopedAccess(..) => "scoped access",
            Expr::Some(..) => "some",
            Expr::Tuple(..) => "tuple",
            Expr::Type(..) => "type",
            Expr::TypeAnnotated(..) => "type-annotated expression",
            Expr::UnaryOp(..) => "unary operation",
            Expr::Unsafe(..) => "unsafe",
            Expr::While(..) => "while",
        }
    }

    pub fn is_missing(&self) -> bool {
        matches!(self, Expr::Missing(_))
    }
}
