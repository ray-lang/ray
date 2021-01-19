use crate::{
    ast::token::{IntegerBase, Token, TokenKind},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Source,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Integer {
        value: String,
        base: IntegerBase,
        size: usize,
        signed: bool,
    },
    Float {
        value: String,
        size: usize,
    },
    String(String),
    ByteString(String),
    Byte(String),
    Char(String),
    Bool(bool),
    UnicodeEscSeq(String),
    Unit,
    Nil,
}

impl Literal {
    pub fn new_int(value: i64) -> Literal {
        Literal::Integer {
            value: value.to_string(),
            base: IntegerBase::Decimal,
            size: 0,
            signed: true,
        }
    }

    pub fn new_uint(value: u64) -> Literal {
        Literal::Integer {
            value: value.to_string(),
            base: IntegerBase::Decimal,
            size: 0,
            signed: false,
        }
    }

    pub fn from_token(token: Token, fp: &FilePath) -> RayResult<Literal> {
        Ok(match token.kind {
            TokenKind::Integer {
                value,
                base,
                suffix,
            } => {
                let (size, signed) = if let Some(suffix) = suffix {
                    let s = suffix.trim_start_matches('_');
                    let span = token.span;
                    let parsed = s[1..].parse::<usize>();
                    let size = parsed.as_ref().map_err(|e| RayError {
                        msg: e.to_string(),
                        kind: RayErrorKind::Parse,
                        src: vec![Source {
                            span: Some(span),
                            filepath: fp.clone(),
                        }],
                    })?;
                    (*size, s.starts_with("i"))
                } else {
                    (0, true)
                };
                Literal::Integer {
                    value,
                    base,
                    size,
                    signed,
                }
            }
            TokenKind::Float { value, suffix } => {
                let size = if let Some(suffix) = suffix {
                    let s = suffix.trim_start_matches('_');
                    if !s.starts_with('f') {
                        return Err(RayError {
                            msg: format!("invalid prefix for float {}", s),
                            kind: RayErrorKind::Parse,
                            src: vec![Source {
                                span: Some(token.span),
                                filepath: fp.clone(),
                            }],
                        });
                    }

                    let parsed = s[1..].parse::<usize>();
                    let span = token.span;
                    *parsed.as_ref().map_err(|e| RayError {
                        msg: e.to_string(),
                        kind: RayErrorKind::Parse,
                        src: vec![Source {
                            span: Some(span),
                            filepath: fp.clone(),
                        }],
                    })?
                } else {
                    0
                };
                Literal::Float { value, size }
            }
            TokenKind::Bool(b) => Literal::Bool(b),
            TokenKind::UnicodeEscSeq(s) => Literal::UnicodeEscSeq(s),
            TokenKind::Nil => Literal::Nil,
            _ => unreachable!(),
        })
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Integer {
                value,
                base,
                size,
                signed,
            } => {
                let prefix = match base {
                    IntegerBase::Binary => "0b",
                    IntegerBase::Hex => "0x",
                    IntegerBase::Octal => "0o",
                    _ => "",
                };
                let sign = if !signed { "u" } else { "" };
                let suffix = if *size != 0 {
                    format!("_{}{}", sign, size)
                } else if sign != "" {
                    format!("_{}", sign)
                } else {
                    "".to_string()
                };
                write!(f, "(int {}{}{})", prefix, value, suffix)
            }
            Literal::Float { value, size } => write!(
                f,
                "(float {}{})",
                value,
                format!(
                    "_f{}",
                    if *size != 0 {
                        format!("{}", size)
                    } else {
                        "".to_string()
                    }
                ),
            ),
            Literal::String(s) => write!(f, "(string \"{}\")", s),
            Literal::ByteString(s) => write!(f, "(bytestring \"{}\")", s),
            Literal::Byte(s) => write!(f, "(byte '{}')", s),
            Literal::Char(s) => write!(f, "(char '{}')", s),
            Literal::UnicodeEscSeq(s) => write!(f, "(unicode \"{}\")", s),
            Literal::Bool(b) => write!(f, "(bool {})", b),
            Literal::Unit => write!(f, "()"),
            Literal::Nil => write!(f, "nil"),
        }
    }
}
