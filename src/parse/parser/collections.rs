use super::{ExprResult, ParseContext, Parser};

use crate::ast::{token::TokenKind, Expr, List, Trailing, ValueKind};

impl Parser<'_> {
    pub(crate) fn parse_array_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let lbrack_span = self.expect_sp(TokenKind::LeftBracket)?;
        let seq = self.parse_expr_seq(
            ValueKind::RValue,
            Trailing::Allow,
            Some(TokenKind::RightBracket),
            ctx,
        )?;
        let rbrack_span = self.expect_sp(TokenKind::RightBracket)?;
        let span = lbrack_span.extend_to(&rbrack_span);
        Ok(self.mk_expr(
            Expr::List(List {
                items: seq.items,
                lbrack_span,
                rbrack_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }
}
