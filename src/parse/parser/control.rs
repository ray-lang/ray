use super::Restrictions;

use crate::ast;
use crate::ast::token::TokenKind;
use crate::parse::{ParseContext, ParseResult, Parser};
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_if(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond = Box::new(self.parse_expr(&ctx)?);
        let then = Box::new(self.parse_block(&ctx)?);
        let mut end = then.span.end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = if peek!(self, TokenKind::If) {
                self.parse_if(&ctx)?
            } else {
                self.parse_block(&ctx)?
            };
            end = e.span.end;
            Some(Box::new(e))
        } else {
            None
        };

        Ok(self.mk_expr(
            ast::ExprKind::If(ast::If { cond, then, els }),
            Span { start, end },
        ))
    }

    pub(crate) fn parse_ternary_expr(
        &mut self,
        then: ast::Expr,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IF_ELSE;
        let start = self.expect_start(TokenKind::If)?;
        let cond = Box::new(self.parse_expr(&ctx)?);
        let mut end = cond.span.end;

        let els = if peek!(self, TokenKind::Else) {
            self.expect(TokenKind::Else)?;
            let e = self.parse_expr(&ctx)?;
            end = e.span.end;
            Some(Box::new(e))
        } else {
            None
        };

        Ok(self.mk_expr(
            ast::ExprKind::If(ast::If {
                then: Box::new(then),
                cond,
                els,
            }),
            Span { start, end },
        ))
    }

    pub(crate) fn parse_for(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let for_span = self.expect_sp(TokenKind::For)?;
        let pat = self.parse_pattern(ctx)?;
        let in_span = self.expect_sp(TokenKind::In)?;
        let expr = self.parse_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let span = for_span.extend_to(&body.span);

        Ok(self.mk_expr(
            ast::ExprKind::For(ast::For {
                expr: Box::new(expr),
                body: Box::new(body),
                pat,
                for_span,
                in_span,
            }),
            span,
        ))
    }

    pub(crate) fn parse_while(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let while_span = self.expect_sp(TokenKind::While)?;
        let cond = self.parse_expr(ctx)?;
        let body = self.parse_block(ctx)?;

        let span = while_span.extend_to(&body.span);

        Ok(self.mk_expr(
            ast::ExprKind::While(ast::While {
                cond: Box::new(cond),
                body: Box::new(body),
                while_span,
            }),
            span,
        ))
    }

    pub(crate) fn parse_loop(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let loop_span = self.expect_sp(TokenKind::Loop)?;
        let body = self.parse_block(ctx)?;
        let span = loop_span.extend_to(&body.span);

        Ok(self.mk_expr(
            ast::ExprKind::Loop(ast::Loop {
                body: Box::new(body),
                loop_span,
            }),
            span,
        ))
    }
}
