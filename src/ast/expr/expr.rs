use std::{collections::HashSet, fmt::Debug};

use crate::ast::{
    Assign, BinOp, Block, Call, Cast, Closure, Curly, Dot, Fn, For, If, Index, List, Literal, Loop,
    Name, Node, Path, Range, Sequence, Type, UnaryOp, While,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Assign(Assign<Info>),
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
                Expr::Labeled(label, ex) => format!("({}: {})", label, ex.to_string()),
                Expr::Literal(ex) => ex.to_string(),
                Expr::Loop(ex) => ex.to_string(),
                Expr::Name(ex) => ex.to_string(),
                Expr::Path(ex) => ex.to_string(),
                Expr::Paren(ex) => ex.to_string(),
                Expr::Range(ex) => ex.to_string(),
                Expr::Return(ex) => ex.as_ref().map_or_else(
                    || "(return)".to_string(),
                    |ex| format!("(return {})", ex.to_string())
                ),
                Expr::Sequence(ex) => ex.to_string(),
                Expr::Tuple(ex) => format!("(tuple {})", ex.to_string()),
                Expr::Type(ex) => ex.to_string(),
                Expr::UnaryOp(ex) => ex.to_string(),
                Expr::Unsafe(ex) => format!("(unsafe {})", ex.to_string()),
                Expr::While(ex) => ex.to_string(),
            }
        )
    }
}

// impl<Info> PartialEq for Expr<Info>
// where
//     T: PartialEq,
//     Info: PartialEq,
// {
//     fn eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (Expr::List(x), Expr::List(y)) => x == y,
//             (Expr::Assign(x), Expr::Assign(y)) => x == y,
//             (Expr::BinOp(x), Expr::BinOp(y)) => x == y,
//             (Expr::Block(x), Expr::Block(y)) => x == y,
//             (Expr::Break(x), Expr::Break(y)) => x == y,
//             (Expr::Call(x), Expr::Call(y)) => x == y,
//             (Expr::Cast(x), Expr::Cast(y)) => x == y,
//             (Expr::Closure(x), Expr::Closure(y)) => x == y,
//             (Expr::Curly(x), Expr::Curly(y)) => x == y,
//             (Expr::DefaultValue(x), Expr::DefaultValue(y)) => x == y,
//             (Expr::Dot(x), Expr::Dot(y)) => x == y,
//             (Expr::Fn(x), Expr::Fn(y)) => x == y,
//             (Expr::For(x), Expr::For(y)) => x == y,
//             (Expr::If(x), Expr::If(y)) => x == y,
//             (Expr::Index(x), Expr::Index(y)) => x == y,
//             (Expr::Labeled(x), Expr::Labeled(y)) => x == y,
//             (Expr::Literal(x), Expr::Literal(y)) => x == y,
//             (Expr::Loop(x), Expr::Loop(y)) => x == y,
//             (Expr::Name(x), Expr::Name(y)) => x == y,
//             (Expr::Path(x), Expr::Path(y)) => x == y,
//             (Expr::Paren(x), Expr::Paren(y)) => x == y,
//             (Expr::Range(x), Expr::Range(y)) => x == y,
//             (Expr::Return(x), Expr::Return(y)) => x == y,
//             (Expr::Sequence(x), Expr::Sequence(y)) => x == y,
//             (Expr::Tuple(x), Expr::Tuple(y)) => x == y,
//             (Expr::Type(x), Expr::Type(y)) => x == y,
//             (Expr::UnaryOp(x), Expr::UnaryOp(y)) => x == y,
//             (Expr::Unsafe(x), Expr::Unsafe(y)) => x == y,
//             (Expr::While(x), Expr::While(y)) => x == y,
//         }
//     }
// }

impl<Info> Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn get_vars(&self) -> HashSet<&String> {
        todo!()
        // let walk = Visitor::from(self);
        // let mut set = HashSet::new();
        // for ex in walk {
        //     match &ex {
        //         Expr::Name(n) => {
        //             set.insert(&n.name);
        //         }
        //         Expr::Curly(c) => {
        //             for el in c.elements.iter() {
        //                 match &el.kind {
        //                     CurlyElementKind::Name(n) => set.insert(&n.name),
        //                     CurlyElementKind::Labeled(n, _) => set.insert(&n.name),
        //                 };
        //             }
        //         }
        //         _ => continue,
        //     }
        // }
        // set
    }

    pub fn get_name(&self) -> Option<String> {
        match &self {
            Expr::Name(n) => Some(n.name.clone()),
            Expr::Fn(f) => f.sig.name.clone(),
            Expr::Path(p) => Some(p.to_string()),
            Expr::Assign(_)
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
            Expr::UnaryOp(..) => "unary operation",
            Expr::Unsafe(..) => "unsafe",
            Expr::While(..) => "while",
        }
    }
}
