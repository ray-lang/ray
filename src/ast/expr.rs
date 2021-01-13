use std::collections::HashSet;

use crate::span::Source;

use super::{
    visitor::Visitor, Assign, BinOp, Block, Call, Cast, Closure, Curly, CurlyElementKind, Dot, Fn,
    For, Id, If, Index, List, Literal, Loop, Name, Path, Range, Sequence, Type, UnaryOp, While,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Assign(Assign),
    BinOp(BinOp),
    Block(Block),
    Break(Option<Box<Expr>>),
    Call(Call),
    Cast(Cast),
    Closure(Closure),
    Curly(Curly),
    DefaultValue(Box<Expr>),
    Dot(Dot),
    Fn(Fn),
    For(For),
    If(If),
    Index(Index),
    Labeled(Box<Expr>, Box<Expr>),
    List(List),
    Literal(Literal),
    Loop(Loop),
    Name(Name),
    Path(Path),
    Paren(Box<Expr>),
    Range(Range),
    Return(Option<Box<Expr>>),
    Sequence(Sequence),
    Tuple(Sequence),
    Type(Type),
    UnaryOp(UnaryOp),
    Unsafe(Box<Expr>),
    While(While),
}

impl ExprKind {
    pub fn desc(&self) -> &'static str {
        match self {
            ExprKind::List(..) => "array",
            ExprKind::Assign(..) => "assign",
            ExprKind::BinOp(..) => "binary operation",
            ExprKind::Block(..) => "block",
            ExprKind::Break(..) => "break",
            ExprKind::Call(..) => "call",
            ExprKind::Cast(..) => "cast",
            ExprKind::Closure(..) => "closure",
            ExprKind::Curly(..) => "curly",
            ExprKind::DefaultValue(..) => "default value",
            ExprKind::Dot(..) => "dot",
            ExprKind::Fn(..) => "function",
            ExprKind::For(..) => "for",
            ExprKind::If(..) => "if",
            ExprKind::Index(..) => "index",
            ExprKind::Labeled(..) => "labeled",
            ExprKind::Literal(..) => "literal",
            ExprKind::Loop(..) => "loop",
            ExprKind::Name(..) => "name",
            ExprKind::Path(..) => "path",
            ExprKind::Paren(..) => "paren",
            ExprKind::Range(..) => "range",
            ExprKind::Return(..) => "return",
            ExprKind::Sequence(..) => "sequence",
            ExprKind::Tuple(..) => "tuple",
            ExprKind::Type(..) => "type",
            ExprKind::UnaryOp(..) => "unary operation",
            ExprKind::Unsafe(..) => "unsafe",
            ExprKind::While(..) => "while",
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub id: Id,
    pub src: Source,
    pub doc: Option<String>,
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self.kind {
                ExprKind::List(ref ex) => ex.to_string(),
                ExprKind::Assign(ref ex) => ex.to_string(),
                ExprKind::BinOp(ref ex) => ex.to_string(),
                ExprKind::Block(ref ex) => ex.to_string(),
                ExprKind::Break(ref ex) => ex.as_ref().map_or_else(
                    || "(break)".to_string(),
                    |ex| format!("(break {})", ex.to_string())
                ),
                ExprKind::Call(ref ex) => ex.to_string(),
                ExprKind::Cast(ref ex) => ex.to_string(),
                ExprKind::Closure(ref ex) => ex.to_string(),
                ExprKind::Curly(ref ex) => ex.to_string(),
                ExprKind::DefaultValue(ref ex) => ex.to_string(),
                ExprKind::Dot(ref ex) => ex.to_string(),
                ExprKind::Fn(ref ex) => ex.to_string(),
                ExprKind::For(ref ex) => ex.to_string(),
                ExprKind::If(ref ex) => ex.to_string(),
                ExprKind::Index(ref ex) => ex.to_string(),
                ExprKind::Labeled(ref label, ref ex) => format!("({}: {})", label, ex.to_string()),
                ExprKind::Literal(ref ex) => ex.to_string(),
                ExprKind::Loop(ref ex) => ex.to_string(),
                ExprKind::Name(ref ex) => ex.to_string(),
                ExprKind::Path(ref ex) => ex.to_string(),
                ExprKind::Paren(ref ex) => ex.to_string(),
                ExprKind::Range(ref ex) => ex.to_string(),
                ExprKind::Return(ref ex) => ex.as_ref().map_or_else(
                    || "(return)".to_string(),
                    |ex| format!("(return {})", ex.to_string())
                ),
                ExprKind::Sequence(ref ex) => ex.to_string(),
                ExprKind::Tuple(ref ex) => format!("(tuple {})", ex.to_string()),
                ExprKind::Type(ref ex) => ex.to_string(),
                ExprKind::UnaryOp(ref ex) => ex.to_string(),
                ExprKind::Unsafe(ref ex) => format!("(unsafe {})", ex.to_string()),
                ExprKind::While(ref ex) => ex.to_string(),
            }
        )
    }
}

impl Expr {
    pub fn get_vars(&self) -> HashSet<&String> {
        let walk = Visitor::from(self);
        let mut set = HashSet::new();
        for ex in walk {
            match &ex.kind {
                ExprKind::Name(n) => {
                    set.insert(&n.name);
                }
                ExprKind::Curly(c) => {
                    for el in c.elements.iter() {
                        match &el.kind {
                            CurlyElementKind::Name(n) => set.insert(&n.name),
                            CurlyElementKind::Labeled(n, _) => set.insert(&n.name),
                        };
                    }
                }
                _ => continue,
            }
        }
        set
    }

    pub fn get_name(&self) -> Option<String> {
        match &self.kind {
            ExprKind::Name(n) => Some(n.name.clone()),
            ExprKind::Fn(f) => f.sig.name.clone(),
            ExprKind::Path(p) => Some(p.to_string()),
            ExprKind::Assign(_)
            | ExprKind::BinOp(_)
            | ExprKind::Block(_)
            | ExprKind::Break(_)
            | ExprKind::Call(_)
            | ExprKind::Cast(_)
            | ExprKind::Closure(_)
            | ExprKind::Curly(_)
            | ExprKind::DefaultValue(_)
            | ExprKind::Dot(_)
            | ExprKind::For(_)
            | ExprKind::If(_)
            | ExprKind::Index(_)
            | ExprKind::Labeled(_, _)
            | ExprKind::Literal(_)
            | ExprKind::List(_)
            | ExprKind::Loop(_)
            | ExprKind::Paren(_)
            | ExprKind::Range(_)
            | ExprKind::Return(_)
            | ExprKind::Sequence(_)
            | ExprKind::Tuple(_)
            | ExprKind::Type(_)
            | ExprKind::UnaryOp(_)
            | ExprKind::Unsafe(_)
            | ExprKind::While(_) => None,
        }
    }
}
