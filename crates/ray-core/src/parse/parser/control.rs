use super::{
    ExprResult, ParsedExpr, Parser, Recover, RecoveryCtx, Restrictions, context::ParseContext,
};

use crate::ast::{Expr, For, If, Loop, While, token::TokenKind};
use ray_shared::span::Span;

impl Parser<'_> {
    pub(crate) fn parse_pre_block_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::NO_CURLY_EXPR;
        ctx.description = Some("parse pre block expression".to_string());
        log::debug!("in new context: parse pre block expression");
        self.parse_expr(&ctx)
    }

    pub(crate) fn parse_if(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        ctx.description = Some("parse if expression".to_string());
        log::debug!("in new context: parse if expression");

        let if_span = self.expect_keyword(TokenKind::If, &ctx)?;
        let start = if_span.start;
        let cond_start = self.lex.position();
        let cond_expr = self.parse_pre_block_expr(&ctx).recover_with_ctx(
            self,
            RecoveryCtx::expr(Some(&TokenKind::LeftCurly)).with_ternary_sensitive(true),
            |parser, cond_end| parser.missing_expr(cond_start, cond_end, &ctx),
        );
        let cond = Box::new(cond_expr);
        if cond.is_missing() {
            // If the condition is missing, we can't continue parsing the if statement
            let then = Box::new(self.missing_expr(start, start, &ctx));
            return Ok(self.mk_expr(
                Expr::If(If {
                    cond,
                    then,
                    els: None,
                }),
                Span { start, end: start },
                ctx.path.clone(),
            ));
        }

        let block_start = self.lex.position();
        let then_expr = self.parse_block(&ctx).recover_with_ctx(
            self,
            RecoveryCtx::stmt(Some(&TokenKind::Else))
                .with_newline(true)
                .with_decl_stops(false),
            |parser, block_end| parser.missing_expr(block_start, block_end, &ctx),
        );
        let mut end = self.srcmap.span_of(&then_expr).end;
        let then = Box::new(then_expr);

        let els = if peek!(self, TokenKind::Else) {
            let else_start = self.lex.position();
            let else_expr = (|| -> ExprResult {
                self.expect_keyword(TokenKind::Else, &ctx)?;
                if peek!(self, TokenKind::If) {
                    self.parse_if(&ctx)
                } else {
                    self.parse_block(&ctx)
                }
            })()
            .recover_with_ctx(
                self,
                RecoveryCtx::stmt(Some(&TokenKind::Else))
                    .with_newline(true)
                    .with_decl_stops(false),
                |parser, else_end| parser.missing_expr(else_start, else_end, &ctx),
            );
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

    pub(crate) fn parse_ternary_expr(
        &mut self,
        then: ParsedExpr,
        ctx: &ParseContext,
    ) -> ExprResult {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        ctx.description = Some("parse ternary expression".to_string());

        let if_span = self.expect_keyword(TokenKind::If, &ctx)?;
        let start = if_span.start;
        let cond_start = self.lex.position();
        let cond_expr = self.parse_expr(&ctx).recover_with_ctx(
            self,
            RecoveryCtx::expr(Some(&TokenKind::Else)).with_ternary_sensitive(true),
            |parser, cond_end| parser.missing_expr(cond_start, cond_end, &ctx),
        );
        let mut end = self.srcmap.span_of(&cond_expr).end;
        let cond = Box::new(cond_expr);

        let els = if peek!(self, TokenKind::Else) {
            let else_start = self.lex.position();
            let e = (|| -> ExprResult {
                self.expect_keyword(TokenKind::Else, &ctx)?;
                self.parse_expr(&ctx)
            })()
            .recover_with_ctx(
                self,
                RecoveryCtx::expr(None).with_ternary_sensitive(true),
                |parser, else_end| parser.missing_expr(else_start, else_end, &ctx),
            );
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
        let parser = &mut self.with_scope(ctx).with_description("parse for loop");
        let ctx = &parser.ctx_clone();

        let for_span = parser.expect_keyword(TokenKind::For, ctx)?;
        let pat_start = parser.lex.position();
        let pat = parser
            .parse_pattern_with_stop(Some(&TokenKind::In), ctx)
            .recover_with_ctx(
                parser,
                RecoveryCtx::stmt(Some(&TokenKind::In))
                    .with_newline(true)
                    .with_decl_stops(false),
                |parser, pat_end| parser.missing_pattern(pat_start, pat_end, ctx),
            );

        let in_start = parser.lex.position();
        let in_span = parser.expect_keyword(TokenKind::In, ctx).recover_with_ctx(
            parser,
            RecoveryCtx::stmt(Some(&TokenKind::LeftCurly))
                .with_newline(true)
                .with_decl_stops(false),
            |_, in_end| Span {
                start: in_start,
                end: in_end,
            },
        );

        let expr_start = parser.lex.position();
        let mut lookahead = 0;
        let mut next_kind = parser.peek_kind();
        while matches!(next_kind, TokenKind::NewLine) {
            lookahead += 1;
            next_kind = parser.peek_kind_at(lookahead);
        }

        let expr = if matches!(next_kind, TokenKind::LeftCurly | TokenKind::EOF) {
            Err(parser.parse_error(
                "expected iterable expression after `in`".to_string(),
                Span {
                    start: expr_start,
                    end: expr_start,
                },
                ctx,
            ))
            .recover_with_ctx(
                parser,
                RecoveryCtx::expr(Some(&TokenKind::LeftCurly)).with_ternary_sensitive(false),
                |parser, expr_end| parser.missing_expr(expr_start, expr_end, ctx),
            )
        } else {
            parser.parse_pre_block_expr(ctx).recover_with_ctx(
                parser,
                RecoveryCtx::expr(Some(&TokenKind::LeftCurly)).with_ternary_sensitive(false),
                |parser, expr_end| parser.missing_expr(expr_start, expr_end, ctx),
            )
        };

        let body_start = parser.lex.position();
        let body = parser.parse_block(ctx).recover_with_ctx(
            parser,
            RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                .with_newline(true)
                .with_decl_stops(false),
            |parser, body_end| parser.missing_expr(body_start, body_end, ctx),
        );

        let body_span = parser.srcmap.span_of(&body);
        let span = for_span.extend_to(&body_span);

        Ok(parser.mk_expr(
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
        let parser = &mut self.with_scope(ctx).with_description("parse while loop");
        let ctx = &parser.ctx_clone();

        let while_span = parser.expect_keyword(TokenKind::While, ctx)?;
        let cond_start = parser.lex.position();
        let cond = parser.parse_pre_block_expr(ctx).recover_with_ctx(
            parser,
            RecoveryCtx::expr(Some(&TokenKind::LeftCurly)).with_ternary_sensitive(false),
            |parser, cond_end| parser.missing_expr(cond_start, cond_end, ctx),
        );
        let body_start = parser.lex.position();
        let body = parser.parse_block(ctx).recover_with_ctx(
            parser,
            RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                .with_newline(true)
                .with_decl_stops(false),
            |parser, body_end| parser.missing_expr(body_start, body_end, ctx),
        );

        let body_span = parser.srcmap.span_of(&body);
        let span = while_span.extend_to(&body_span);

        Ok(parser.mk_expr(
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
        let parser = &mut self.with_scope(ctx).with_description("parse loop");
        let ctx = &parser.ctx_clone();

        let loop_span = parser.expect_keyword(TokenKind::Loop, ctx)?;
        let body_start = parser.lex.position();
        let body = parser.parse_block(ctx).recover_with_ctx(
            parser,
            RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                .with_newline(true)
                .with_decl_stops(false),
            |parser, body_end| parser.missing_expr(body_start, body_end, ctx),
        );

        let body_span = parser.srcmap.span_of(&body);
        let span = loop_span.extend_to(&body_span);

        Ok(parser.mk_expr(
            Expr::Loop(Loop {
                body: Box::new(body),
                loop_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }
}
