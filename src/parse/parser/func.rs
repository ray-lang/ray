use super::{ParseContext, ParseResult, Parser, Restrictions};

use crate::ast;
use crate::ast::token::TokenKind;
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_fn(&mut self, only_sigs: bool, ctx: &ParseContext) -> ParseResult<ast::Fn> {
        let sig = self.parse_fn_sig(ctx)?;
        let start = sig.span.start;
        let mut end = sig.span.end;
        let body = if !only_sigs {
            let b = if expect_if!(self, TokenKind::FatArrow) {
                self.parse_expr(ctx)?
            } else {
                self.parse_block(ctx)?
            };
            end = b.src.span.unwrap().end;
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

    pub(crate) fn parse_fn_sig(&mut self, ctx: &ParseContext) -> ParseResult<ast::FnSig> {
        self.parse_fn_sig_with_param(ctx, |this| this.parse_params(ctx))
    }

    pub(crate) fn parse_trait_fn_sig(&mut self, ctx: &ParseContext) -> ParseResult<ast::FnSig> {
        self.parse_fn_sig_with_param(ctx, |this| this.parse_trait_fn_params(ctx))
    }

    pub(crate) fn parse_fn_sig_with_param<F>(
        &mut self,
        ctx: &ParseContext,
        f: F,
    ) -> ParseResult<ast::FnSig>
    where
        F: Fn(&mut Parser) -> ParseResult<(Vec<ast::FnParam>, Span)>,
    {
        let modifiers = self.parse_modifiers()?;
        let start = self.expect_start(TokenKind::Fn)?;
        let name = self.parse_fn_name(ctx)?;
        let ty_params = self.parse_ty_params()?;
        let (params, param_span) = f(self)?;
        let mut end = param_span.end;
        let ret_ty = if expect_if!(self, TokenKind::Arrow) {
            let t = self.parse_ty()?;
            end = t.span.unwrap().end;
            Some(t)
        } else {
            None
        };

        let qualifiers = self.parse_where_clause()?;

        Ok(ast::FnSig {
            name,
            params,
            ty_params,
            ret_ty,
            modifiers,
            qualifiers,
            ty: None, // this will be populated later
            decorators: None,
            doc_comment: None,
            span: Span { start, end },
        })
    }

    pub(crate) fn parse_fn_name(&mut self, ctx: &ParseContext) -> ParseResult<Option<String>> {
        Ok(if peek!(self, TokenKind::Identifier {..}) {
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
        })
    }

    pub(crate) fn parse_params(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<ast::FnParam>, Span)> {
        self.parse_params_with(ctx, |this| {
            Ok(ast::FnParam::Name(this.parse_name_with_type()?))
        })
    }

    pub(crate) fn parse_trait_fn_params(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<ast::FnParam>, Span)> {
        self.parse_params_with(ctx, |this| Ok(this.parse_trait_fn_param()?))
    }

    fn parse_params_with<F>(
        &mut self,
        ctx: &ParseContext,
        f: F,
    ) -> ParseResult<(Vec<ast::FnParam>, Span)>
    where
        F: Fn(&mut Parser) -> ParseResult<ast::FnParam>,
    {
        let (lparen_tok, lp_span) = self.expect(TokenKind::LeftParen)?;
        let start = lp_span.start;
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;

        let mut params = vec![];
        loop {
            if peek!(self, TokenKind::RightParen) {
                break;
            }

            let mut param = f(self)?;
            if expect_if!(self, TokenKind::Equals) {
                let d = self.parse_expr(&ctx)?;
                param = ast::FnParam::DefaultValue(Box::new(param), Box::new(d));
            }
            params.push(param);

            if !peek!(self, TokenKind::RightParen) {
                self.expect(TokenKind::Comma)?;
            }
        }

        let end = self.expect_matching(&lparen_tok, TokenKind::RightParen)?;
        Ok((params, Span { start, end }))
    }
}