use super::{ParseContext, ParseResult, Parser, Restrictions};

use crate::ast;
use crate::ast::token::TokenKind;
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_fn(&mut self, only_sigs: bool, ctx: &ParseContext) -> ParseResult<ast::Fn> {
        let (sig, span) = self.parse_fn_sig(ctx)?;
        let start = span.start;
        let mut end = span.end;
        let body = if !only_sigs {
            let b = if expect_if!(self, TokenKind::FatArrow) {
                self.parse_expr(ctx)?
            } else {
                self.parse_block(ctx)?
            };
            end = b.span.end;
            Some(b)
        } else {
            None
        };

        let span = Span { start, end };
        Ok(ast::Fn {
            sig,
            body: body.map(|b| Box::new(b)),
            span,
        })
    }

    pub(crate) fn parse_fn_sig(&mut self, ctx: &ParseContext) -> ParseResult<(ast::FnSig, Span)> {
        let modifiers = self.parse_modifiers()?;

        let start = self.expect_start(TokenKind::Fn)?;
        let name = if peek!(self, TokenKind::Identifier {..}) {
            let (n, _) = self.expect_id()?;
            Some(n)
        } else if let Some((op, tok_count)) = self.peek_infix_op(ctx)? {
            self.lex.consume_count(tok_count);
            Some(op.to_string())
        } else if let Some((op, tok_count)) = self.peek_prefix_op()? {
            self.lex.consume_count(tok_count);
            Some(op.to_string())
        } else {
            None
        };
        let ty_params = self.parse_ty_params()?;
        let (params, param_span) = self.parse_params(ctx)?;
        let mut end = param_span.end;
        let ret_ty = if expect_if!(self, TokenKind::Arrow) {
            let t = self.parse_ty()?;
            end = t.span.unwrap().end;
            Some(t)
        } else {
            None
        };
        Ok((
            ast::FnSig {
                name,
                params,
                ty_params,
                ret_ty,
                modifiers,
                ty: None, // this will be populated later
                decorators: None,
                doc_comment: None,
            },
            Span { start, end },
        ))
    }

    fn parse_params(&mut self, ctx: &ParseContext) -> ParseResult<(Vec<ast::Name>, Span)> {
        let mut names = Vec::new();
        let (lparen_tok, lp_span) = self.expect(TokenKind::LeftParen)?;
        let start = lp_span.start;
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;

        loop {
            if peek!(self, TokenKind::RightParen) {
                break;
            }

            let mut name = self.parse_name_with_type()?;
            name.default = if expect_if!(self, TokenKind::Equals) {
                let d = self.parse_expr(&ctx)?;
                name.span.end = d.span.end;
                Some(Box::new(d))
            } else {
                None
            };

            names.push(name);

            if !peek!(self, TokenKind::RightParen) {
                self.expect(TokenKind::Comma)?;
            }
        }

        let end = self.expect_matching(&lparen_tok, TokenKind::RightParen)?;
        Ok((names, Span { start, end }))
    }
}
