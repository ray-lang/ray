use super::{ParseContext, ParseResult, Parser, Recover, Restrictions};

use crate::{
    ast::{self, FnParam, FuncSig, Missing, Name, Node, Path, token::TokenKind},
    span::Span,
};

impl Parser<'_> {
    pub(crate) fn parse_fn(
        &mut self,
        only_sigs: bool,
        ctx: &ParseContext,
    ) -> ParseResult<(ast::Func, Span)> {
        let mut sig = self.parse_fn_sig(ctx)?;
        let start = sig.span.start;
        let mut end = sig.span.end;

        let mut ctx = ctx.clone();
        ctx.path = sig.path.value.clone();

        let body = if !only_sigs {
            let body_start = self.lex.position();
            let expr = if expect_if!(self, TokenKind::FatArrow) {
                self.parse_expr(&ctx).recover_with(
                    self,
                    Some(&TokenKind::RightCurly),
                    |parser, body_end| parser.missing_expr(body_start, body_end, &ctx),
                )
            } else {
                self.parse_block(&ctx).recover_with(
                    self,
                    Some(&TokenKind::RightCurly),
                    |parser, body_end| parser.missing_block_expr(body_start, body_end, &ctx),
                )
            };
            end = self.srcmap.span_of(&expr).end;
            sig.has_body = true;
            Some(expr)
        } else {
            None
        };

        Ok((
            ast::Func {
                sig,
                body: body.map(|b| Box::new(b)),
            },
            Span { start, end },
        ))
    }

    pub(crate) fn parse_fn_sig(&mut self, ctx: &ParseContext) -> ParseResult<FuncSig> {
        self.parse_fn_sig_with_param(ctx, |this| this.parse_params(ctx))
    }

    pub(crate) fn parse_trait_fn_sig(&mut self, ctx: &ParseContext) -> ParseResult<FuncSig> {
        self.parse_fn_sig_with_param(ctx, |this| this.parse_trait_fn_params(ctx))
    }

    pub(crate) fn parse_fn_sig_with_param<F>(
        &mut self,
        ctx: &ParseContext,
        parse_params: F,
    ) -> ParseResult<FuncSig>
    where
        F: Fn(&mut Parser) -> ParseResult<(Vec<Node<FnParam>>, Span)>,
    {
        let modifiers = self.parse_modifiers()?;
        let fn_span = self.expect_keyword(TokenKind::Fn, ctx)?;
        let start = fn_span.start;
        let name: Option<(String, Span)> = self.parse_fn_name(ctx)?;
        let is_anon = name.is_none();
        let path = if let Some((name, span)) = &name {
            let path = ctx.path.append(name);
            self.mk_node(path, *span)
        } else {
            Node::new(ctx.path.append("<anon>"))
        };

        let ty_params =
            self.parse_ty_params(ctx)
                .recover_seq(self, Some(&TokenKind::RightParen), |_| None);
        let (params, param_span) = parse_params(self)?;
        let mut end = param_span.end;
        let ret_ty = if self.expect_if_operator(TokenKind::Arrow)?.is_some() {
            let t = self
                .parse_type_annotation(Some(&TokenKind::LeftCurly), ctx)
                .map(|t| t.into_mono());
            end = t.span().unwrap().end;
            Some(t)
        } else {
            None
        };

        let qualifiers = self.parse_where_clause(ctx)?;

        Ok(FuncSig {
            path,
            params,
            ty_params,
            ret_ty,
            modifiers,
            qualifiers,
            ty: None, // this will be populated later
            doc_comment: None,
            is_method: false,
            is_anon,
            has_body: false,
            span: Span { start, end },
        })
    }

    pub(crate) fn parse_fn_name(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Option<(String, Span)>> {
        if peek!(self, TokenKind::Identifier { .. }) {
            return Ok(Some(self.expect_id(ctx)?));
        }

        let (op_str, tok_count) = if let Some((op, tok_count)) = self.peek_infix_op(ctx)? {
            (op.to_string(), tok_count)
        } else if let Some((op, tok_count)) = self.peek_prefix_op()? {
            (op.to_string(), tok_count)
        } else {
            return Ok(None);
        };

        let (prec_and_toks, _) = self.lex.consume_count(tok_count);
        let span = prec_and_toks
            .iter()
            .map(|(_, tok)| tok.span)
            .reduce(|a, b| a.extend_to(&b))
            .unwrap();
        Ok(Some((op_str, span)))
    }

    pub(crate) fn parse_params(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Node<FnParam>>, Span)> {
        let path = ctx.path.clone();
        self.parse_params_with(ctx, |this| Ok(this.parse_fn_param(ctx, &path)?))
    }

    pub(crate) fn parse_trait_fn_params(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Node<FnParam>>, Span)> {
        self.parse_params_with(ctx, |this| Ok(this.parse_trait_fn_param(ctx)?))
    }

    pub(crate) fn parse_fn_param(
        &mut self,
        ctx: &ParseContext,
        path: &Path,
    ) -> ParseResult<Node<FnParam>> {
        self.parse_name_with_type(Some(&TokenKind::RightParen), ctx)
            .map(|name| {
                let span = self.srcmap.span_of(&name);
                self.mk_node_with_path(FnParam::Name(name.value), span, path.clone())
            })
    }

    pub(crate) fn parse_trait_fn_param(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Node<FnParam>> {
        let (name, span) = self.expect_id(ctx)?;
        self.expect(TokenKind::Colon, ctx)?;
        let ty = self.parse_type_annotation(Some(&TokenKind::Comma), ctx);
        Ok(self.mk_node(FnParam::Name(Name::typed(name, ty)), span))
    }

    fn parse_params_with<F>(
        &mut self,
        ctx: &ParseContext,
        f: F,
    ) -> ParseResult<(Vec<Node<FnParam>>, Span)>
    where
        F: Fn(&mut Parser) -> ParseResult<Node<FnParam>>,
    {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        ctx.description = Some("parse params".to_string());

        let lparen_tok = self.expect(TokenKind::LeftParen, &ctx)?;
        let start = lparen_tok.span.start;

        let mut params = vec![];
        loop {
            if peek!(self, TokenKind::RightParen) {
                break;
            }

            let mut param =
                f(self).recover_with(self, Some(&TokenKind::RightParen), |parser, recovered| {
                    let span = Span {
                        start: recovered,
                        end: recovered,
                    };
                    let info = Missing::new("parameter", Some(ctx.path.clone()));
                    let placeholder = Name::new("_");
                    parser.mk_node(FnParam::Missing { info, placeholder }, span)
                });
            if expect_if!(self, TokenKind::Equals) {
                let d = self.parse_expr(&ctx)?;
                let span = self
                    .srcmap
                    .span_of(&param)
                    .extend_to(&self.srcmap.span_of(&d));
                param = self.mk_node(FnParam::DefaultValue(Box::new(param), Box::new(d)), span);
            }
            params.push(param);

            if !peek!(self, TokenKind::RightParen) {
                self.expect(TokenKind::Comma, &ctx)?;
            }
        }

        let end = self.expect_matching(&lparen_tok, TokenKind::RightParen, &ctx)?;
        Ok((params, Span { start, end }))
    }
}
