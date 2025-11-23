use std::cmp::PartialEq;
use std::fmt;
use std::string::String;

use serde::{Deserialize, Serialize};

use crate::ast::modifier::Modifier;
use ray_shared::span::Span;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum IntegerBase {
    Decimal,
    Binary,
    Octal,
    Hex,
}

impl IntegerBase {
    pub fn prefix(&self) -> &str {
        match self {
            IntegerBase::Binary => "0b",
            IntegerBase::Octal => "0o",
            IntegerBase::Hex => "0x",
            IntegerBase::Decimal => "",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum CommentKind {
    Line,
    Doc,
    ModuleDoc,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum TokenKind {
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
    /// default
    Default,
    /// impl
    Impl,
    /// object
    Object,
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
    /// new
    New,
    /// box
    Bx,

    Modifier(Modifier),

    // atoms
    Integer {
        value: String,
        base: IntegerBase,
        suffix: Option<String>,
    },
    Float {
        value: String,
        suffix: Option<String>,
    },
    Bool(bool),
    UnicodeEscSeq(String),
    PrefixedIdent(char, String),
    Identifier(String),

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

    // delimeters
    /// (
    LeftParen,
    /// )
    RightParen,
    /// {
    LeftCurly,
    /// }
    RightCurly,
    /// [
    LeftBracket,
    /// ]
    RightBracket,

    /// '
    SingleQuote,
    /// "
    DoubleQuote,
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

    // special
    NewLine,
    Whitespace,
    Comment {
        content: String,
        kind: CommentKind,
    },
    Illegal(String),
    EOF,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind.to_string())
    }
}

impl TokenKind {
    pub fn desc(&self) -> &str {
        match self {
            TokenKind::Integer { .. } => "integer",
            TokenKind::Float { .. } => "float",
            TokenKind::UnicodeEscSeq(_) => "unicode escape sequence",
            TokenKind::Illegal(_) => "illegal",
            TokenKind::Identifier(_) | TokenKind::PrefixedIdent(..) => "identifier",
            TokenKind::Modifier(_) => "modifier",
            TokenKind::UpperFn => "`Fn`",
            TokenKind::Mut => "`mut`",
            TokenKind::Const => "`const`",
            TokenKind::Fn => "`fn`",
            TokenKind::If => "`if`",
            TokenKind::Unless => "`unless`",
            TokenKind::Else => "`else`",
            TokenKind::Then => "`then`",
            TokenKind::Break => "`break`",
            TokenKind::Return => "`return`",
            TokenKind::Async => "`async`",
            TokenKind::Extern => "`extern`",
            TokenKind::TypeAlias => "`typealias`",
            TokenKind::Struct => "`struct`",
            TokenKind::Enum => "`enum`",
            TokenKind::Trait => "`trait`",
            TokenKind::Default => "`default`",
            TokenKind::Impl => "`impl`",
            TokenKind::Object => "`object`",
            TokenKind::Nil => "`nil`",
            TokenKind::With => "`with`",
            TokenKind::Import => "`import`",
            TokenKind::As => "`as`",
            TokenKind::While => "`while`",
            TokenKind::Loop => "`loop`",
            TokenKind::For => "`for`",
            TokenKind::In => "`in`",
            TokenKind::Is => "`is`",
            TokenKind::Where => "`where`",
            TokenKind::New => "`new`",
            TokenKind::Bx => "`box`",
            TokenKind::Equals => "`=`",
            TokenKind::Gt => "`>`",
            TokenKind::Lt => "`<`",
            TokenKind::Plus => "`+`",
            TokenKind::Minus => "`-`",
            TokenKind::Asterisk => "`*`",
            TokenKind::Slash => "`/`",
            TokenKind::Percent => "`%`",
            TokenKind::Exclamation => "`!`",
            TokenKind::Ampersand => "`&`",
            TokenKind::Pipe => "`|`",
            TokenKind::Caret => "`^`",
            TokenKind::Tilde => "`~`",
            TokenKind::LeftParen => "`(`",
            TokenKind::RightParen => "`)`",
            TokenKind::LeftCurly => "`{`",
            TokenKind::RightCurly => "`}`",
            TokenKind::LeftBracket => "`[`",
            TokenKind::RightBracket => "`]`",
            TokenKind::Ellipsis => "`...`",
            TokenKind::RangeInclusive => "`..=`",
            TokenKind::RangeExclusive => "`..<`",
            TokenKind::Dot => "`.`",
            TokenKind::SingleQuote => "`'`",
            TokenKind::DoubleQuote => "`\"`",
            TokenKind::Question => "`?`",
            TokenKind::Comma => "`,`",
            TokenKind::Semi => "`;`",
            TokenKind::Colon => "`:`",
            TokenKind::DoubleColon => "`::`",
            TokenKind::Arrow => "`->`",
            TokenKind::FatArrow => "`=>`",
            TokenKind::At => "`@`",
            TokenKind::Dollar => "`$`",
            TokenKind::Underscore => "`_`",
            TokenKind::Hash => "`#`",
            TokenKind::NewLine => "newline",
            TokenKind::Whitespace => "whitespace",
            TokenKind::Comment { kind, .. } => match kind {
                CommentKind::ModuleDoc => "`//!`",
                CommentKind::Doc => "`///`",
                CommentKind::Line => "`//`",
            },
            TokenKind::Bool(b) => {
                if *b {
                    "`true`"
                } else {
                    "`false`"
                }
            }
            TokenKind::EOF => "EOF",
        }
    }

    pub fn similar_to(&self, other: &TokenKind) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(other)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            TokenKind::Integer {
                value,
                base,
                suffix,
            } => {
                let prefix = base.prefix();
                if let Some(suffix) = suffix {
                    format!("{}{}{}", prefix, value, suffix)
                } else {
                    format!("{}{}", prefix, value)
                }
            }
            TokenKind::Float { value, suffix } => {
                if let Some(suffix) = suffix {
                    format!("{}{}", value, suffix)
                } else {
                    value.clone()
                }
            }
            TokenKind::Illegal(c) => c.to_string(),
            TokenKind::PrefixedIdent(c, id) => format!("{}{}", c, id),
            TokenKind::Identifier(id) => id.clone(),
            TokenKind::UnicodeEscSeq(id) => id.clone(),
            TokenKind::Modifier(m) => m.to_string(),
            TokenKind::UpperFn => "Fn".to_string(),
            TokenKind::Mut => "mut".to_string(),
            TokenKind::Const => "const".to_string(),
            TokenKind::Fn => "fn".to_string(),
            TokenKind::If => "if".to_string(),
            TokenKind::Unless => "unless".to_string(),
            TokenKind::Else => "else".to_string(),
            TokenKind::Then => "then".to_string(),
            TokenKind::Return => "return".to_string(),
            TokenKind::Break => "break".to_string(),
            TokenKind::Async => "async".to_string(),
            TokenKind::Extern => "extern".to_string(),
            TokenKind::Struct => "struct".to_string(),
            TokenKind::Enum => "enum".to_string(),
            TokenKind::Trait => "trait".to_string(),
            TokenKind::Default => "default".to_string(),
            TokenKind::Impl => "impl".to_string(),
            TokenKind::Object => "object".to_string(),
            TokenKind::TypeAlias => "typealias".to_string(),
            TokenKind::With => "with".to_string(),
            TokenKind::Nil => "nil".to_string(),
            TokenKind::Import => "import".to_string(),
            TokenKind::As => "as".to_string(),
            TokenKind::For => "for".to_string(),
            TokenKind::While => "while".to_string(),
            TokenKind::Loop => "loop".to_string(),
            TokenKind::In => "in".to_string(),
            TokenKind::Is => "is".to_string(),
            TokenKind::Where => "where".to_string(),
            TokenKind::New => "new".to_string(),
            TokenKind::Bx => "box".to_string(),
            TokenKind::Equals => "=".to_string(),
            TokenKind::Gt => ">".to_string(),
            TokenKind::Lt => "<".to_string(),
            TokenKind::Plus => "+".to_string(),
            TokenKind::Minus => "-".to_string(),
            TokenKind::Asterisk => "*".to_string(),
            TokenKind::Slash => "/".to_string(),
            TokenKind::Percent => "%".to_string(),
            TokenKind::Exclamation => "!".to_string(),
            TokenKind::Ampersand => "&".to_string(),
            TokenKind::Pipe => "|".to_string(),
            TokenKind::Caret => "^".to_string(),
            TokenKind::Tilde => "~".to_string(),
            TokenKind::LeftParen => "(".to_string(),
            TokenKind::RightParen => ")".to_string(),
            TokenKind::LeftCurly => "{".to_string(),
            TokenKind::RightCurly => "}".to_string(),
            TokenKind::LeftBracket => "[".to_string(),
            TokenKind::RightBracket => "]".to_string(),
            TokenKind::Ellipsis => "...".to_string(),
            TokenKind::RangeInclusive => "..=".to_string(),
            TokenKind::RangeExclusive => "..<".to_string(),
            TokenKind::Dot => ".".to_string(),
            TokenKind::SingleQuote => "'".to_string(),
            TokenKind::DoubleQuote => "\"".to_string(),
            TokenKind::Question => "?".to_string(),
            TokenKind::Comma => ",".to_string(),
            TokenKind::Semi => ";".to_string(),
            TokenKind::Colon => ":".to_string(),
            TokenKind::DoubleColon => "::".to_string(),
            TokenKind::Arrow => "->".to_string(),
            TokenKind::FatArrow => "=>".to_string(),
            TokenKind::At => "@".to_string(),
            TokenKind::Dollar => "$".to_string(),
            TokenKind::Hash => "#".to_string(),
            TokenKind::Underscore => "_".to_string(),
            TokenKind::NewLine => "\\n".to_string(),
            TokenKind::Whitespace => " ".to_string(),
            TokenKind::Comment { kind, .. } => match kind {
                CommentKind::ModuleDoc => "//!".to_string(),
                CommentKind::Doc => "///".to_string(),
                CommentKind::Line => "//".to_string(),
            },
            TokenKind::Bool(b) => (if *b { "true" } else { "false" }).to_string(),
            TokenKind::EOF => "EOF".to_string(),
        };

        write!(f, "{}", s)
    }
}
