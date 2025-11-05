use std::{fmt, ops::Deref};

use crate::ast::{Node, token::TokenKind};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Associativity {
    /// The operator is left-associative
    Left,
    /// The operator is right-associative
    Right,
    /// The operator is not associative
    None,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrefixOp {
    /// +
    Positive,
    /// -
    Negative,
    /// *
    Deref,
    /// &
    Ref,
    /// !
    Not,
    /// ~
    BitNot,
    /// <-
    Receive,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InfixOp {
    /// ==
    Eq,
    /// !=
    NotEq,
    /// <
    Lt,
    /// >
    Gt,
    /// >=
    GtEq,
    /// <=
    LtEq,
    /// +
    Add,
    /// -
    Sub,
    /// /
    Div,
    /// %
    Mod,
    /// *
    Mul,
    /// **
    Pow,
    /// &&
    And,
    /// ||
    Or,
    /// <<
    ShiftLeft,
    /// >>
    ShiftRight,
    /// &
    BitAnd,
    /// |
    BitOr,
    /// ^
    BitXor,
    /// ..<
    RangeExclusive,
    /// ..=
    RangeInclusive,
    /// ,
    Comma,
    /// :
    Colon,
    /// as (casting operator)
    As,
    /// else (nil coelescing operator)
    Else,
    /// =
    Assign,
    // ?=
    AssignOp(Box<Node<InfixOp>>),
}

impl fmt::Display for InfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl InfixOp {
    pub fn is(name: &str) -> bool {
        matches!(
            name,
            "==" | "!="
                | "<"
                | ">"
                | ">="
                | "<="
                | "+"
                | "-"
                | "/"
                | "%"
                | "*"
                | "**"
                | "&&"
                | "||"
                | "&"
                | "|"
                | "^"
                | "<<"
                | ">>"
        )
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            InfixOp::Eq => "==",
            InfixOp::NotEq => "!=",
            InfixOp::Lt => "<",
            InfixOp::Gt => ">",
            InfixOp::GtEq => ">=",
            InfixOp::LtEq => "<=",
            InfixOp::Add => "+",
            InfixOp::Sub => "-",
            InfixOp::Div => "/",
            InfixOp::Mod => "%",
            InfixOp::Mul => "*",
            InfixOp::Pow => "**",
            InfixOp::And => "&&",
            InfixOp::Or => "||",
            InfixOp::BitAnd => "&",
            InfixOp::BitOr => "|",
            InfixOp::BitXor => "^",
            InfixOp::ShiftLeft => "<<",
            InfixOp::ShiftRight => ">>",
            InfixOp::RangeExclusive => "..<",
            InfixOp::RangeInclusive => "..=",
            InfixOp::As => "as",
            InfixOp::Else => "else",
            InfixOp::Comma => ",",
            InfixOp::Colon => ":",
            InfixOp::Assign => "=",
            InfixOp::AssignOp(op) => match op.as_ref().deref() {
                InfixOp::Add => "+=",
                InfixOp::Sub => "-=",
                InfixOp::Div => "/=",
                InfixOp::Mod => "%=",
                InfixOp::Mul => "*=",
                InfixOp::Pow => "**=",
                InfixOp::And => "&&=",
                InfixOp::Or => "||=",
                InfixOp::ShiftLeft => "<<=",
                InfixOp::ShiftRight => ">>=",
                InfixOp::BitAnd => "&=",
                InfixOp::BitOr => "|=",
                InfixOp::BitXor => "^=",
                _ => unreachable!("found invalid assign op {}", op),
            },
        }
    }

    pub fn precedence(&self) -> usize {
        use InfixOp::*;
        match self {
            Colon => 17,
            As => 16,
            Pow => 15,
            Mul | Div | Mod => 14,
            Add | Sub => 13,
            ShiftLeft | ShiftRight => 12,
            BitAnd => 11,
            BitXor => 10,
            BitOr => 9,
            Else => 8,
            Lt | Gt | LtEq | GtEq | Eq | NotEq => 7,
            And => 6,
            Or => 5,
            RangeExclusive | RangeInclusive => 4,
            Comma => 3,
            Assign | AssignOp(_) => 2,
        }
    }

    /// Gets the associativity of this operator
    pub fn associativity(&self) -> Associativity {
        use InfixOp::*;
        match self {
            Assign | AssignOp(_) => Associativity::Right,
            Colon | Comma | As | Else | Pow | Mul | Div | Mod | Add | Sub | ShiftLeft
            | ShiftRight | BitAnd | BitXor | BitOr | Lt | Gt | LtEq | GtEq | Eq | NotEq | And
            | Or => Associativity::Left,
            RangeExclusive | RangeInclusive => Associativity::None,
        }
    }

    pub(crate) fn matches_token_kind(&self, kind: &TokenKind) -> bool {
        use TokenKind::*;
        match self {
            InfixOp::Eq => matches!(kind, Equals),
            InfixOp::NotEq => matches!(kind, Exclamation),
            InfixOp::Lt | InfixOp::LtEq | InfixOp::ShiftLeft => matches!(kind, Lt),
            InfixOp::Gt | InfixOp::GtEq | InfixOp::ShiftRight => matches!(kind, Gt),
            InfixOp::Add => matches!(kind, Plus),
            InfixOp::Sub => matches!(kind, Minus),
            InfixOp::Div => matches!(kind, Slash),
            InfixOp::Mod => matches!(kind, Percent),
            InfixOp::Mul | InfixOp::Pow => matches!(kind, Asterisk),
            InfixOp::And => matches!(kind, Ampersand),
            InfixOp::Or => matches!(kind, Pipe),
            InfixOp::BitAnd => matches!(kind, Ampersand),
            InfixOp::BitOr => matches!(kind, Pipe),
            InfixOp::BitXor => matches!(kind, Caret),
            InfixOp::RangeExclusive => matches!(kind, RangeExclusive),
            InfixOp::RangeInclusive => matches!(kind, RangeInclusive),
            InfixOp::As => matches!(kind, As),
            InfixOp::Else => matches!(kind, Else),
            InfixOp::Comma => matches!(kind, Comma),
            InfixOp::Colon => matches!(kind, Colon),
            InfixOp::Assign => matches!(kind, Equals),
            InfixOp::AssignOp(inner) => inner.matches_token_kind(kind),
        }
    }
}

impl fmt::Display for PrefixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl PrefixOp {
    pub fn is(name: &str) -> bool {
        matches!(name, "+" | "-" | "*" | "&" | "!" | "~" | "<-")
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            PrefixOp::Positive => "+",
            PrefixOp::Negative => "-",
            PrefixOp::Deref => "*",
            PrefixOp::Ref => "&",
            PrefixOp::Not => "!",
            PrefixOp::BitNot => "~",
            PrefixOp::Receive => "<-",
        }
    }
}
