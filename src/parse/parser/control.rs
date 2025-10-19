use super::{ExprResult, ParseContext, ParsedExpr, Parser, Recover, Restrictions};

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
        let if_span = self.expect_keyword(TokenKind::If)?;
        let start = if_span.start;
        let cond_start = self.lex.position();
        let cond_expr = self.parse_pre_block_expr(&ctx).recover_with(
            self,
            Some(&TokenKind::LeftCurly),
            |parser, cond_end| parser.missing_expr(cond_start, cond_end, &ctx),
        );
        let cond = Box::new(cond_expr);

        let block_start = self.lex.position();
        let then_expr = self.parse_block(&ctx).recover_with(
            self,
            Some(&TokenKind::Else),
            |parser, block_end| parser.missing_block_expr(block_start, block_end, &ctx),
        );
        let mut end = self.srcmap.span_of(&then_expr).end;
        let then = Box::new(then_expr);

        let els = if peek!(self, TokenKind::Else) {
            let else_start = self.lex.position();
            let else_expr = (|| -> ExprResult {
                self.expect_keyword(TokenKind::Else)?;
                if peek!(self, TokenKind::If) {
                    self.parse_if(&ctx)
                } else {
                    self.parse_block(&ctx)
                }
            })()
            .recover_with(self, None, |parser, else_end| {
                parser.missing_block_expr(else_start, else_end, &ctx)
            });
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
        let if_span = self.expect_keyword(TokenKind::If)?;
        let start = if_span.start;
        let cond_start = self.lex.position();
        let cond_expr =
            self.parse_expr(&ctx)
                .recover_with(self, Some(&TokenKind::Else), |parser, cond_end| {
                    parser.missing_expr(cond_start, cond_end, &ctx)
                });
        let mut end = self.srcmap.span_of(&cond_expr).end;
        let cond = Box::new(cond_expr);

        let els = if peek!(self, TokenKind::Else) {
            let else_start = self.lex.position();
            let e = (|| -> ExprResult {
                self.expect_keyword(TokenKind::Else)?;
                self.parse_expr(&ctx)
            })()
            .recover_with(self, None, |parser, else_end| {
                parser.missing_expr(else_start, else_end, &ctx)
            });
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
        let for_span = self.expect_keyword(TokenKind::For)?;
        let pat_start = self.lex.position();
        let pat =
            self.parse_pattern(ctx)
                .recover_with(self, Some(&TokenKind::In), |parser, pat_end| {
                    parser.missing_pattern(pat_start, pat_end, ctx)
                });

        let in_start = self.lex.position();
        let in_span = self.expect_keyword(TokenKind::In).recover_with(
            self,
            Some(&TokenKind::LeftCurly),
            |_, in_end| Span {
                start: in_start,
                end: in_end,
            },
        );

        let expr_start = self.lex.position();
        let mut lookahead = 0;
        let mut next_kind = self.peek_kind();
        while matches!(next_kind, TokenKind::NewLine) {
            lookahead += 1;
            next_kind = self.peek_kind_at(lookahead);
        }

        let expr = if matches!(next_kind, TokenKind::LeftCurly | TokenKind::EOF) {
            Err(self.parse_error(
                "expected iterable expression after `in`".to_string(),
                Span {
                    start: expr_start,
                    end: expr_start,
                },
            ))
            .recover_with(self, Some(&TokenKind::LeftCurly), |parser, expr_end| {
                parser.missing_expr(expr_start, expr_end, ctx)
            })
        } else {
            self.parse_pre_block_expr(ctx).recover_with(
                self,
                Some(&TokenKind::LeftCurly),
                |parser, expr_end| parser.missing_expr(expr_start, expr_end, ctx),
            )
        };

        let body_start = self.lex.position();
        let body = self
            .parse_block(ctx)
            .recover_with(self, None, |parser, body_end| {
                parser.missing_block_expr(body_start, body_end, ctx)
            });

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
        let while_span = self.expect_keyword(TokenKind::While)?;
        let cond_start = self.lex.position();
        let cond = self.parse_pre_block_expr(ctx).recover_with(
            self,
            Some(&TokenKind::LeftCurly),
            |parser, cond_end| parser.missing_expr(cond_start, cond_end, ctx),
        );
        let body_start = self.lex.position();
        let body = self
            .parse_block(ctx)
            .recover_with(self, None, |parser, body_end| {
                parser.missing_block_expr(body_start, body_end, ctx)
            });

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
        let loop_span = self.expect_keyword(TokenKind::Loop)?;
        let body_start = self.lex.position();
        let body = self
            .parse_block(ctx)
            .recover_with(self, None, |parser, body_end| {
                parser.missing_block_expr(body_start, body_end, ctx)
            });

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
