use crate::{
    ast::{
        Path, PrefixOp,
        token::{IntegerBase, Token, TokenKind},
    },
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
        explicit_sign: Option<PrefixOp>,
    },
    Float {
        value: String,
        size: usize,
        explicit_sign: Option<PrefixOp>,
    },
    String(String),
    ByteString(String),
    Byte(String),
    Char(char),
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
            explicit_sign: None,
        }
    }

    pub fn new_uint(value: u64) -> Literal {
        Literal::Integer {
            value: value.to_string(),
            base: IntegerBase::Decimal,
            size: 0,
            signed: false,
            explicit_sign: None,
        }
    }

    pub fn from_token(token: Token, fp: FilePath, src_module: &Path) -> RayResult<Literal> {
        Ok(match token.kind {
            TokenKind::Integer {
                value,
                base,
                suffix,
            } => {
                let (size, signed) = if let Some(suffix) = suffix {
                    let suffix = suffix.trim_start_matches('_');
                    let span = token.span;
                    let raw_size = &suffix[1..];
                    let size = if raw_size.len() > 0 {
                        let parsed = raw_size.parse::<usize>();
                        *parsed.as_ref().map_err(|e| RayError {
                            msg: e.to_string(),
                            kind: RayErrorKind::Parse,
                            src: vec![Source::new(fp, span, Path::new(), src_module.clone())],
                            context: Some(format!("integer literal raw suffix: {suffix}")),
                        })?
                    } else {
                        0
                    };
                    (size, suffix.starts_with("i"))
                } else {
                    (0, true)
                };
                Literal::Integer {
                    value,
                    base,
                    size,
                    signed,
                    explicit_sign: None,
                }
            }
            TokenKind::Float { value, suffix } => {
                let size = if let Some(suffix) = suffix {
                    let s = suffix.trim_start_matches('_');
                    if !s.starts_with('f') {
                        return Err(RayError {
                            msg: format!("invalid prefix for float {}", s),
                            kind: RayErrorKind::Parse,
                            src: vec![Source::new(
                                fp.clone(),
                                token.span,
                                Path::new(),
                                src_module.clone(),
                            )],
                            context: Some(format!("float literal suffix: {s}")),
                        });
                    }

                    let parsed = s[1..].parse::<usize>();
                    let span = token.span;
                    *parsed.as_ref().map_err(|e| RayError {
                        msg: e.to_string(),
                        kind: RayErrorKind::Parse,
                        src: vec![Source::new(
                            fp.clone(),
                            span,
                            Path::new(),
                            src_module.clone(),
                        )],
                        context: Some(format!("float literal suffix: {s}")),
                    })?
                } else {
                    0
                };
                Literal::Float {
                    value,
                    size,
                    explicit_sign: None,
                }
            }
            TokenKind::Bool(b) => Literal::Bool(b),
            TokenKind::UnicodeEscSeq(s) => Literal::UnicodeEscSeq(s),
            TokenKind::Nil => Literal::Nil,
            _ => unreachable!(),
        })
    }

    pub fn with_explicit_sign(&mut self, op: PrefixOp) {
        match self {
            Literal::Integer {
                signed,
                explicit_sign,
                ..
            } => {
                *signed = true;
                *explicit_sign = Some(op);
            }
            Literal::Float { explicit_sign, .. } => {
                *explicit_sign = Some(op);
            }
            Literal::String(_)
            | Literal::ByteString(_)
            | Literal::Byte(_)
            | Literal::Char(_)
            | Literal::Bool(_)
            | Literal::UnicodeEscSeq(_)
            | Literal::Unit
            | Literal::Nil => unreachable!("invalid use of negative sign with literal: {:?}", self),
        }
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
                explicit_sign,
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
                let explicit_sign = if let Some(explicit_sign) = explicit_sign {
                    format!("{}", explicit_sign)
                } else {
                    "".to_string()
                };
                write!(f, "(int {}{}{}{})", explicit_sign, prefix, value, suffix)
            }
            Literal::Float {
                value,
                size,
                explicit_sign,
            } => write!(
                f,
                "(float {}{}{})",
                if let Some(explicit_sign) = explicit_sign {
                    format!("{}", explicit_sign)
                } else {
                    "".to_string()
                },
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
