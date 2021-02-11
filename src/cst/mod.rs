use std::ops::{Deref, DerefMut};

use crate::{
    ast::{token::TokenKind, Path},
    span::{parsed::Parsed, Source},
};

mod op;

pub use op::*;

#[derive(Debug, Clone, Copy)]
pub enum Delimiter {
    Paren,
    Curly,
    Bracket,
    SingleQuote,
    DoubleQuote,
}

#[derive(Debug, Clone)]
pub enum Keyword {
    /// mut
    Mut,
    /// const
    Const,
    /// fn
    Fn,
    /// Fn
    UpperFn,
    /// if
    If,
    /// unless
    Unless,
    /// else
    Else,
    /// then
    Then,
    /// return
    Return,
    /// break
    Break,
    /// async
    Async,
    /// extern
    Extern,
    /// struct
    Struct,
    /// enum
    Enum,
    /// trait
    Trait,
    /// impl
    Impl,
    /// type
    TypeAlias,
    /// nil
    Nil,
    /// import
    Import,
    /// with
    With,
    /// as
    As,
    /// for
    For,
    /// while
    While,
    /// loop
    Loop,
    /// in
    In,
    /// is
    Is,
    /// where
    Where,
    /// asm
    Asm,
    /// true
    True,
    /// false
    False,
}

pub enum Char {
    /// =
    Equals,
    /// >
    Gt,
    /// <
    Lt,
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Asterisk,
    /// /
    Slash,
    /// %
    Percent,
    /// &
    Ampersand,
    /// |
    Pipe,
    /// !
    Exclamation,
    /// ^
    Caret,
    /// ~
    Tilde,
    /// ?
    Question,
    /// .
    Dot,
    /// ..=
    RangeInclusive,
    /// ..<
    RangeExclusive,
    /// ...
    Ellipsis,
    /// ,
    Comma,
    /// ;
    Semi,
    /// :
    Colon,
    /// ::
    DoubleColon,
    /// ->
    Arrow,
    /// =>
    FatArrow,
    /// @
    At,
    /// $
    Dollar,
    /// _
    Underscore,
    /// #
    Hash,
}

#[derive(Debug, Clone)]
pub struct Delimited {
    delimiters: (Option<Parsed<Delimiter>>, Option<Parsed<Delimiter>>),
    nodes: Vec<Parsed<Node>>,
}

impl Delimited {
    pub fn new(
        delimiters: (Option<Parsed<Delimiter>>, Option<Parsed<Delimiter>>),
        nodes: Vec<Parsed<Node>>,
    ) -> Delimited {
        Delimited { delimiters, nodes }
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Delimited(Parsed<Delimited>),
    Identifier(Parsed<String>),
    Keyword(Parsed<Keyword>),
    Prefix(Parsed<PrefixOp>, Parsed<Box<Node>>),
    Postfix(Parsed<Box<Node>>, Parsed<PostfixOp>),
    Infix(Parsed<Box<Node>>, Parsed<InfixOp>, Parsed<Box<Node>>),
}

#[derive(Debug, Clone)]
pub struct Module {
    path: Path,
    src: Source,
    root: Parsed<Node>,
}

impl Module {
    pub fn new(path: Path, src: Source, root: Parsed<Node>) -> Module {
        Module { path, src, root }
    }
}
