use super::{ParseContext, ParseResult, Parser};
use crate::ast;
use crate::ast::token::TokenKind;

impl Parser {
    pub(crate) fn parse_array_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let lbrack_span = self.expect_sp(TokenKind::LeftBracket)?;
        let seq = self.parse_expr_seq(
            ast::ValueKind::RValue,
            ast::Trailing::Allow,
            Some(TokenKind::RightBracket),
            ctx,
        )?;
        let rbrack_span = self.expect_sp(TokenKind::RightBracket)?;
        let span = lbrack_span.extend_to(&rbrack_span);
        Ok(self.mk_expr(
            ast::ExprKind::List(ast::List {
                items: seq.items,
                lbrack_span,
                rbrack_span,
            }),
            span,
        ))
    }
}
