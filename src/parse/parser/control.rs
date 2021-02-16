use super::{ExprResult, ParseContext, ParsedExpr, Parser, Restrictions};

use crate::{
    ast::{token::TokenKind, Expr, For, If, Loop, While},
    span::Span,
};

impl Parser<'_> {
    pub(crate) fn parse_pre_block_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::NO_CURLY_EXPR;
        self.parse_expr(&ctx)
    }

    pub(crate) fn parse_if(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond = Box::new(self.parse_pre_block_expr(&ctx)?);
        let then = Box::new(self.parse_block(&ctx)?);
        let mut end = self.srcmap.span_of(&then).end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = if peek!(self, TokenKind::If) {
                self.parse_if(&ctx)?
            } else {
                self.parse_block(&ctx)?
            };
            end = self.srcmap.span_of(&e).end;
            Some(Box::new(e))
        } else {
            None
        };

        Ok(self.mk_expr(
            Expr::If(If { cond, then, els }),
            Span { start, end },
            ctx.path.clone(),
        ))
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
        let mut end = self.srcmap.span_of(&cond).end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = self.parse_expr(&ctx)?;
            end = self.srcmap.span_of(&e).end;
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
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_for(&mut self, ctx: &ParseContext) -> ExprResult {
        let for_span = self.expect_sp(TokenKind::For)?;
        let pat = self.parse_pattern(ctx)?;
        let in_span = self.expect_sp(TokenKind::In)?;
        let expr = self.parse_pre_block_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let body_span = self.srcmap.span_of(&body);
        let span = for_span.extend_to(&body_span);

        Ok(self.mk_expr(
            Expr::For(For {
                expr: Box::new(expr),
                body: Box::new(body),
                pat,
                for_span,
                in_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_while(&mut self, ctx: &ParseContext) -> ExprResult {
        let while_span = self.expect_sp(TokenKind::While)?;
        let cond = self.parse_pre_block_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let body_span = self.srcmap.span_of(&body);
        let span = while_span.extend_to(&body_span);

        Ok(self.mk_expr(
            Expr::While(While {
                cond: Box::new(cond),
                body: Box::new(body),
                while_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_loop(&mut self, ctx: &ParseContext) -> ExprResult {
        let loop_span = self.expect_sp(TokenKind::Loop)?;
        let body = self.parse_block(ctx)?;

        let body_span = self.srcmap.span_of(&body);
        let span = loop_span.extend_to(&body_span);

        Ok(self.mk_expr(
            Expr::Loop(Loop {
                body: Box::new(body),
                loop_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }
}
