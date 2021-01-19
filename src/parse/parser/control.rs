use super::{ExprResult, ParseContext, ParsedExpr, Parser, Restrictions};

use crate::{
    ast::{token::TokenKind, Expr, For, If, Loop, While},
    span::Span,
};

impl Parser {
    pub(crate) fn parse_if(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond = Box::new(self.parse_expr(&ctx)?);
        let then = Box::new(self.parse_block(&ctx)?);
        let mut end = then.info.src.span.unwrap().end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = if peek!(self, TokenKind::If) {
                self.parse_if(&ctx)?
            } else {
                self.parse_block(&ctx)?
            };
            end = e.info.src.span.unwrap().end;
            Some(Box::new(e))
        } else {
            None
        };

        Ok(self.mk_expr(Expr::If(If { cond, then, els }), Span { start, end }))
    }

    pub(crate) fn parse_ternary_expr(
        &mut self,
        then: ParsedExpr,
        ctx: &ParseContext,
    ) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond = Box::new(self.parse_expr(&ctx)?);
        let mut end = cond.info.src.span.unwrap().end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = self.parse_expr(&ctx)?;
            end = e.info.src.span.unwrap().end;
            Some(Box::new(e))
        } else {
            None
        };

        Ok(self.mk_expr(
            Expr::If(If {
                then: Box::new(then),
                cond,
                els,
            }),
            Span { start, end },
        ))
    }

    pub(crate) fn parse_for(&mut self, ctx: &ParseContext) -> ExprResult {
        let for_span = self.expect_sp(TokenKind::For)?;
        let pat = self.parse_pattern(ctx)?;
        let in_span = self.expect_sp(TokenKind::In)?;
        let expr = self.parse_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let span = for_span.extend_to(&body.info.src.span.unwrap());

        Ok(self.mk_expr(
            Expr::For(For {
                expr: Box::new(expr),
                body: Box::new(body),
                pat,
                for_span,
                in_span,
            }),
            span,
        ))
    }

    pub(crate) fn parse_while(&mut self, ctx: &ParseContext) -> ExprResult {
        let while_span = self.expect_sp(TokenKind::While)?;
        let cond = self.parse_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let span = while_span.extend_to(&body.info.src.span.unwrap());

        Ok(self.mk_expr(
            Expr::While(While {
                cond: Box::new(cond),
                body: Box::new(body),
                while_span,
            }),
            span,
        ))
    }

    pub(crate) fn parse_loop(&mut self, ctx: &ParseContext) -> ExprResult {
        let loop_span = self.expect_sp(TokenKind::Loop)?;
        let body = self.parse_block(ctx)?;
        let span = loop_span.extend_to(&body.info.src.span.unwrap());

        Ok(self.mk_expr(
            Expr::Loop(Loop {
                body: Box::new(body),
                loop_span,
            }),
            span,
        ))
    }
}
