use super::{ExprResult, ParseContext, ParsedExpr, Parser, Restrictions};

use crate::{
    ast::{Expr, For, If, Loop, While, token::TokenKind},
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
        let cond_start = self.lex.position();
        let cond_expr = match self.parse_pre_block_expr(&ctx) {
            Ok(expr) => expr,
            Err(err) => {
                self.record_parse_error(err);
                let cond_end = self.recover_after_error(Some(&TokenKind::LeftCurly));
                self.placeholder_unit_expr(cond_start, cond_end, &ctx)
            }
        };
        let cond = Box::new(cond_expr);

        let block_start = self.lex.position();
        let then_expr = match self.parse_block(&ctx) {
            Ok(expr) => expr,
            Err(err) => {
                self.record_parse_error(err);
                let block_end = self.recover_after_error(Some(&TokenKind::Else));
                self.placeholder_block_expr(block_start, block_end, &ctx)
            }
        };
        let mut end = self.srcmap.span_of(&then_expr).end;
        let then = Box::new(then_expr);

        let els = if peek!(self, TokenKind::Else) {
            let else_start = self.lex.position();
            if let Err(err) = self.expect(TokenKind::Else) {
                self.record_parse_error(err);
            }
            let else_expr = if peek!(self, TokenKind::If) {
                match self.parse_if(&ctx) {
                    Ok(expr) => expr,
                    Err(err) => {
                        self.record_parse_error(err);
                        let else_end = self.recover_after_error(None);
                        self.placeholder_block_expr(else_start, else_end, &ctx)
                    }
                }
            } else {
                let else_block_start = self.lex.position();
                match self.parse_block(&ctx) {
                    Ok(expr) => expr,
                    Err(err) => {
                        self.record_parse_error(err);
                        let else_end = self.recover_after_error(None);
                        self.placeholder_block_expr(else_block_start, else_end, &ctx)
                    }
                }
            };
            end = self.srcmap.span_of(&else_expr).end;
            Some(Box::new(else_expr))
        } else {
            None
        };

        Ok(self.mk_expr(
            Expr::If(If { cond, then, els }),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    #[allow(dead_code)]
    pub(crate) fn parse_ternary_expr(
        &mut self,
        then: ParsedExpr,
        ctx: &ParseContext,
    ) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond_start = self.lex.position();
        let cond_expr = match self.parse_expr(&ctx) {
            Ok(expr) => expr,
            Err(err) => {
                self.record_parse_error(err);
                let cond_end = self.recover_after_error(Some(&TokenKind::Else));
                self.placeholder_unit_expr(cond_start, cond_end, &ctx)
            }
        };
        let mut end = self.srcmap.span_of(&cond_expr).end;
        let cond = Box::new(cond_expr);

        let els = if peek!(self, TokenKind::Else) {
            if let Err(err) = self.expect(TokenKind::Else) {
                self.record_parse_error(err);
            }
            let else_start = self.lex.position();
            let e = match self.parse_expr(&ctx) {
                Ok(expr) => expr,
                Err(err) => {
                    self.record_parse_error(err);
                    let else_end = self.recover_after_error(None);
                    self.placeholder_unit_expr(else_start, else_end, &ctx)
                }
            };
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
        let pat_start = self.lex.position();
        let pat = match self.parse_pattern(ctx) {
            Ok(pat) => pat,
            Err(err) => {
                self.record_parse_error(err);
                let pat_end = self.recover_after_error(Some(&TokenKind::In));
                self.placeholder_pattern(pat_start, pat_end)
            }
        };

        let in_start = self.lex.position();
        let in_span = match self.expect_sp(TokenKind::In) {
            Ok(span) => span,
            Err(err) => {
                self.record_parse_error(err);
                let in_end = self.recover_after_error(Some(&TokenKind::LeftCurly));
                Span {
                    start: in_start,
                    end: in_end,
                }
            }
        };

        let expr_start = self.lex.position();
        let expr = match self.parse_pre_block_expr(ctx) {
            Ok(expr) => expr,
            Err(err) => {
                self.record_parse_error(err);
                let expr_end = self.recover_after_error(Some(&TokenKind::LeftCurly));
                self.placeholder_unit_expr(expr_start, expr_end, ctx)
            }
        };

        let body_start = self.lex.position();
        let body = match self.parse_block(ctx) {
            Ok(body) => body,
            Err(err) => {
                self.record_parse_error(err);
                let body_end = self.recover_after_error(None);
                self.placeholder_block_expr(body_start, body_end, ctx)
            }
        };

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
        let cond_start = self.lex.position();
        let cond = match self.parse_pre_block_expr(ctx) {
            Ok(expr) => expr,
            Err(err) => {
                self.record_parse_error(err);
                let cond_end = self.recover_after_error(Some(&TokenKind::LeftCurly));
                self.placeholder_unit_expr(cond_start, cond_end, ctx)
            }
        };
        let body_start = self.lex.position();
        let body = match self.parse_block(ctx) {
            Ok(body) => body,
            Err(err) => {
                self.record_parse_error(err);
                let body_end = self.recover_after_error(None);
                self.placeholder_block_expr(body_start, body_end, ctx)
            }
        };

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
        let body_start = self.lex.position();
        let body = match self.parse_block(ctx) {
            Ok(body) => body,
            Err(err) => {
                self.record_parse_error(err);
                let body_end = self.recover_after_error(None);
                self.placeholder_block_expr(body_start, body_end, ctx)
            }
        };

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
