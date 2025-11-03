use super::{ExprResult, Parser, context::ParseContext};

use crate::ast::{Expr, List, TrailingPolicy, ValueKind, token::TokenKind};
use crate::parse::{
    lexer::NewlineMode,
    parser::{context::SeqSpec, Restrictions},
};

impl Parser<'_> {
    pub(crate) fn parse_array_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftBracket, TokenKind::RightBracket)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let (seq, spans) = self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
            parser.parse_expr_seq(ValueKind::RValue, trailing, stop, ctx)
        })?;

        let (l_span, r_span) = spans.expect("array expression must have bracket spans");
        let span = l_span.extend_to(&r_span);
        Ok(self.mk_expr(
            Expr::List(List {
                items: seq.items,
                lbrack_span: l_span,
                rbrack_span: r_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }
}
