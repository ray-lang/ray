use std::fmt::Debug;

use crate::{
    ast::{Node, Path, asm::Asm},
    span::parsed::Parsed,
    typing::ty::TyScheme,
};

use super::{
    Assign, BinOp, Block, Call, Cast, Closure, Curly, Dot, For, Func, If, Index, List, Literal,
    Loop, Name, New, Pattern, Range, Sequence, Tuple, UnaryOp, While,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Assign(Assign),
    Asm(Asm),
    BinOp(BinOp),
    Block(Block),
    Break(Option<Box<Node<Expr>>>),
    Call(Call),
    Cast(Cast),
    Closure(Closure),
    Curly(Curly),
    DefaultValue(Box<Node<Expr>>),
    Dot(Dot),
    Func(Func),
    For(For),
    If(If),
    Index(Index),
    Labeled(Box<Node<Expr>>, Box<Node<Expr>>),
    List(List),
    Literal(Literal),
    Loop(Loop),
    Name(Name),
    New(New),
    Path(Path),
    Pattern(Pattern),
    Paren(Box<Node<Expr>>),
    Range(Range),
    Return(Option<Box<Node<Expr>>>),
    Sequence(Sequence),
    Tuple(Tuple),
    Type(Parsed<TyScheme>),
    TypeAnnotated(Box<Node<Expr>>, Node<Parsed<TyScheme>>),
    UnaryOp(UnaryOp),
    Unsafe(Box<Node<Expr>>),
    While(While),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    LValue,
    RValue,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Trailing {
    Allow,
    Disallow,
    Warn,
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Expr::List(ex) => ex.to_string(),
                Expr::Assign(ex) => ex.to_string(),
                Expr::Asm(ex) => ex.to_string(),
                Expr::BinOp(ex) => ex.to_string(),
                Expr::Block(ex) => ex.to_string(),
                Expr::Break(ex) => ex.as_ref().map_or_else(
                    || "(break)".to_string(),
                    |ex| format!("(break {})", ex.to_string())
                ),
                Expr::Call(ex) => ex.to_string(),
                Expr::Cast(ex) => ex.to_string(),
                Expr::Closure(ex) => ex.to_string(),
                Expr::Curly(ex) => ex.to_string(),
                Expr::DefaultValue(ex) => ex.to_string(),
                Expr::Dot(ex) => ex.to_string(),
                Expr::Func(ex) => ex.to_string(),
                Expr::For(ex) => ex.to_string(),
                Expr::If(ex) => ex.to_string(),
                Expr::Index(ex) => ex.to_string(),
                Expr::Labeled(label, ex) => format!("({}: {})", label, ex),
                Expr::Literal(ex) => ex.to_string(),
                Expr::Loop(ex) => ex.to_string(),
                Expr::Name(ex) => ex.to_string(),
                Expr::New(ex) => ex.to_string(),
                Expr::Path(ex) => ex.to_string(),
                Expr::Pattern(ex) => ex.to_string(),
                Expr::Paren(ex) => ex.to_string(),
                Expr::Range(ex) => ex.to_string(),
                Expr::Return(ex) => ex
                    .as_ref()
                    .map_or_else(|| "(return)".to_string(), |ex| format!("(return {})", ex)),
                Expr::Sequence(ex) => ex.to_string(),
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
    pub fn path(&self) -> Option<Path> {
        match self {
            Expr::Name(n) => Some(n.path.clone()),
            Expr::Func(f) => Some(f.sig.path.clone()),
            Expr::Pattern(p) => p.path().cloned(),
            Expr::Path(p) => Some(p.clone()),
            Expr::Assign(_)
            | Expr::Asm(_)
            | Expr::BinOp(_)
            | Expr::Block(_)
            | Expr::Break(_)
            | Expr::Call(_)
            | Expr::Cast(_)
            | Expr::Closure(_)
            | Expr::Curly(_)
            | Expr::DefaultValue(_)
            | Expr::Dot(_)
            | Expr::For(_)
            | Expr::If(_)
            | Expr::Index(_)
            | Expr::Labeled(_, _)
            | Expr::Literal(_)
            | Expr::List(_)
            | Expr::Loop(_)
            | Expr::New(_)
            | Expr::Paren(_)
            | Expr::Range(_)
            | Expr::Return(_)
            | Expr::Sequence(_)
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
            Expr::Path(p) => Some(p.to_string()),
            Expr::Assign(_)
            | Expr::Asm(_)
            | Expr::BinOp(_)
            | Expr::Block(_)
            | Expr::Break(_)
            | Expr::Call(_)
            | Expr::Cast(_)
            | Expr::Closure(_)
            | Expr::Curly(_)
            | Expr::DefaultValue(_)
            | Expr::Dot(_)
            | Expr::For(_)
            | Expr::If(_)
            | Expr::Index(_)
            | Expr::Labeled(_, _)
            | Expr::Literal(_)
            | Expr::List(_)
            | Expr::Loop(_)
            | Expr::New(_)
            | Expr::Paren(_)
            | Expr::Range(_)
            | Expr::Return(_)
            | Expr::Sequence(_)
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
            Expr::Asm(..) => "asm",
            Expr::BinOp(..) => "binary operation",
            Expr::Block(..) => "block",
            Expr::Break(..) => "break",
            Expr::Call(..) => "call",
            Expr::Cast(..) => "cast",
            Expr::Closure(..) => "closure",
            Expr::Curly(..) => "curly",
            Expr::DefaultValue(..) => "default value",
            Expr::Dot(..) => "dot",
            Expr::Func(..) => "function",
            Expr::For(..) => "for",
            Expr::If(..) => "if",
            Expr::Index(..) => "index",
            Expr::Labeled(..) => "labeled",
            Expr::Literal(..) => "literal",
            Expr::Loop(..) => "loop",
            Expr::Name(..) => "name",
            Expr::New(..) => "new",
            Expr::Pattern(..) => "pattern",
            Expr::Path(..) => "path",
            Expr::Paren(..) => "paren",
            Expr::Range(..) => "range",
            Expr::Return(..) => "return",
            Expr::Sequence(..) => "sequence",
            Expr::Tuple(..) => "tuple",
            Expr::Type(..) => "type",
            Expr::TypeAnnotated(..) => "type-annotated expression",
            Expr::UnaryOp(..) => "unary operation",
            Expr::Unsafe(..) => "unsafe",
            Expr::While(..) => "while",
        }
    }
}
