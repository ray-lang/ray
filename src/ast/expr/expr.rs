use std::{collections::HashSet, fmt::Debug};

use crate::ast::{
    asm::Asm, Assign, BinOp, Block, Call, Cast, Closure, Curly, Dot, Fn, For, If, Index, List,
    Literal, Loop, Name, Node, Path, Range, Sequence, Type, UnaryOp, While,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Assign(Assign<Info>),
    Asm(Asm),
    BinOp(BinOp<Info>),
    Block(Block<Info>),
    Break(Option<Box<Node<Expr<Info>, Info>>>),
    Call(Call<Info>),
    Cast(Cast<Info>),
    Closure(Closure<Info>),
    Curly(Curly<Info>),
    DefaultValue(Box<Node<Expr<Info>, Info>>),
    Dot(Dot<Info>),
    Fn(Fn<Info>),
    For(For<Info>),
    If(If<Info>),
    Index(Index<Info>),
    Labeled(Box<Node<Expr<Info>, Info>>, Box<Node<Expr<Info>, Info>>),
    List(List<Info>),
    Literal(Literal),
    Loop(Loop<Info>),
    Name(Name),
    Path(Path),
    Paren(Box<Node<Expr<Info>, Info>>),
    Range(Range<Info>),
    Return(Option<Box<Node<Expr<Info>, Info>>>),
    Sequence(Sequence<Info>),
    Tuple(Sequence<Info>),
    Type(Type),
    TypeAnnotated(Box<Node<Expr<Info>, Info>>, Node<Type, Info>),
    UnaryOp(UnaryOp<Info>),
    Unsafe(Box<Node<Expr<Info>, Info>>),
    While(While<Info>),
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

impl<Info> std::fmt::Display for Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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
                Expr::Fn(ex) => ex.to_string(),
                Expr::For(ex) => ex.to_string(),
                Expr::If(ex) => ex.to_string(),
                Expr::Index(ex) => ex.to_string(),
                Expr::Labeled(label, ex) => format!("({}: {})", label, ex),
                Expr::Literal(ex) => ex.to_string(),
                Expr::Loop(ex) => ex.to_string(),
                Expr::Name(ex) => ex.to_string(),
                Expr::Path(ex) => ex.to_string(),
                Expr::Paren(ex) => ex.to_string(),
                Expr::Range(ex) => ex.to_string(),
                Expr::Return(ex) => ex
                    .as_ref()
                    .map_or_else(|| "(return)".to_string(), |ex| format!("(return {})", ex)),
                Expr::Sequence(ex) => ex.to_string(),
                Expr::Tuple(ex) => format!("(tuple {})", ex),
                Expr::Type(ex) => ex.to_string(),
                Expr::TypeAnnotated(value, ty) => format!("({} :: {})", value, ty),
                Expr::UnaryOp(ex) => ex.to_string(),
                Expr::Unsafe(ex) => format!("(unsafe {})", ex),
                Expr::While(ex) => ex.to_string(),
            }
        )
    }
}

impl<Info> Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn get_name(&self) -> Option<String> {
        match &self {
            Expr::Name(n) => Some(n.name.clone()),
            Expr::Fn(f) => f.sig.name.clone(),
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
            Expr::Fn(..) => "function",
            Expr::For(..) => "for",
            Expr::If(..) => "if",
            Expr::Index(..) => "index",
            Expr::Labeled(..) => "labeled",
            Expr::Literal(..) => "literal",
            Expr::Loop(..) => "loop",
            Expr::Name(..) => "name",
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
