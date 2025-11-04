use crate::{
    ast::{InfixOp, TrailingPolicy},
    errors::RayError,
};

use super::{Parser, Pos, TokenKind};

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Delimiter {
    Paren,
    Bracket,
    Curly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecoveryStop {
    Guard,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecoveryOutcome {
    Progress { end: Pos },
    Stopped { end: Pos, reason: RecoveryStop },
}

impl RecoveryOutcome {
    pub fn end(self) -> Pos {
        match self {
            RecoveryOutcome::Progress { end }
            | RecoveryOutcome::Stopped { end, .. } => end,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recovered<T> {
    pub value: T,
    pub outcome: RecoveryOutcome,
}

impl<T> Recovered<T> {
    pub fn into_value(self) -> T {
        self.value
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecoveryMode {
    Stmt {
        newline_breaks: bool,
        decl_stops: bool,
    },
    Seq {
        delimiter: Delimiter,
        trailing: TrailingPolicy,
        newline_breaks: bool,
    },
    Expr {
        ternary_sensitive: bool,
        last_op: Option<InfixOp>,
        newline_breaks: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecoveryCtx<'a> {
    pub mode: RecoveryMode,
    pub stop: Option<&'a TokenKind>,
}

impl<'a> RecoveryCtx<'a> {
    pub fn stmt(stop: Option<&'a TokenKind>) -> Self {
        Self {
            mode: RecoveryMode::Stmt {
                newline_breaks: true,
                decl_stops: true,
            },
            stop,
        }
    }

    pub fn seq(
        stop: Option<&'a TokenKind>,
        delimiter: Delimiter,
        trailing: TrailingPolicy,
    ) -> Self {
        Self {
            mode: RecoveryMode::Seq {
                delimiter,
                trailing,
                newline_breaks: false,
            },
            stop,
        }
    }

    pub fn default_seq(stop: Option<&'a TokenKind>) -> Self {
        Self::seq(stop, Delimiter::Paren, TrailingPolicy::Allow)
    }

    pub fn expr(stop: Option<&'a TokenKind>) -> Self {
        Self {
            mode: RecoveryMode::Expr {
                ternary_sensitive: true,
                last_op: None,
                newline_breaks: false,
            },
            stop,
        }
    }

    pub fn with_newline(mut self, newline_breaks: bool) -> Self {
        match &mut self.mode {
            RecoveryMode::Stmt {
                newline_breaks: nb, ..
            }
            | RecoveryMode::Seq {
                newline_breaks: nb, ..
            } => {
                *nb = newline_breaks;
            }
            RecoveryMode::Expr { .. } => {}
        }
        self
    }

    pub fn with_decl_stops(mut self, decl_stops: bool) -> Self {
        if let RecoveryMode::Stmt { decl_stops: ds, .. } = &mut self.mode {
            *ds = decl_stops;
        }
        self
    }

    pub fn with_trailing(mut self, policy: TrailingPolicy) -> Self {
        if let RecoveryMode::Seq { trailing, .. } = &mut self.mode {
            *trailing = policy;
        }
        self
    }

    pub fn with_ternary_sensitive(mut self, ternary_sensitive: bool) -> Self {
        if let RecoveryMode::Expr {
            ternary_sensitive: ts,
            ..
        } = &mut self.mode
        {
            *ts = ternary_sensitive;
        }
        self
    }

    pub fn with_last_op(mut self, op: Option<InfixOp>) -> Self {
        if let RecoveryMode::Expr { last_op, .. } = &mut self.mode {
            *last_op = op;
        }
        self
    }

    pub fn with_newline_breaks(mut self, newline_breaks: bool) -> Self {
        if let RecoveryMode::Expr {
            newline_breaks: nb, ..
        } = &mut self.mode
        {
            *nb = newline_breaks;
        }
        self
    }
}

pub trait Recover<T> {
    fn recover_with_ctx_outcome(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>, RecoveryOutcome) -> T,
    ) -> Recovered<T>;

    fn recover_with_ctx(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>, Pos) -> T,
    ) -> T;

    fn recover_seq_with_ctx(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>) -> T,
    ) -> T;
}

impl<T> Recover<T> for Result<T, RayError> {
    fn recover_with_ctx_outcome(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>, RecoveryOutcome) -> T,
    ) -> Recovered<T> {
        match self {
            Ok(value) => Recovered {
                value,
                outcome: RecoveryOutcome::Progress {
                    end: parser.lex.position(),
                },
            },
            Err(err) => {
                parser.record_parse_error(err);
                let recovered_end = parser.recover_stmt_with_ctx(ctx);
                let value = fallback(parser, RecoveryOutcome::Progress { end: recovered_end });
                Recovered {
                    value,
                    outcome: RecoveryOutcome::Progress {
                        end: recovered_end,
                    },
                }
            }
        }
    }

    fn recover_with_ctx(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>, Pos) -> T,
    ) -> T {
        self.recover_with_ctx_outcome(parser, ctx, |parser, outcome| {
            fallback(parser, outcome.end())
        })
        .into_value()
    }

    fn recover_seq_with_ctx(
        self,
        parser: &mut Parser<'_>,
        ctx: RecoveryCtx<'_>,
        fallback: impl FnOnce(&mut Parser<'_>) -> T,
    ) -> T {
        match self {
            Ok(value) => value,
            Err(err) => {
                parser.record_parse_error(err);
                parser.recover_seq_with_ctx(ctx);
                fallback(parser)
            }
        }
    }
}
