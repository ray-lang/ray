use super::{
    ParseResult, Parser, Recover, RecoveryCtx, Restrictions,
    context::{ParseContext, SeqSpec},
};

use crate::{
    ast::{self, FnParam, FuncSig, Missing, Name, Node, Path, TrailingPolicy, token::TokenKind},
    parse::lexer::NewlineMode,
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
                let parser = &mut self
                    .with_scope(&ctx)
                    .with_description("parse arrow expression")
                    .with_newline_mode(NewlineMode::Suppress);
                let arrow_ctx = parser.ctx_clone();
                parser.parse_expr(&arrow_ctx).recover_with_ctx(
                    parser,
                    RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                        .with_newline(true)
                        .with_decl_stops(false),
                    |parser, body_end| parser.missing_expr(body_start, body_end, &ctx),
                )
            } else {
                self.parse_block(&ctx).recover_with_ctx(
                    self,
                    RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                        .with_newline(true)
                        .with_decl_stops(false),
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
        let mut parser = self
            .with_scope(ctx)
            .with_description("parse function signature");
        let ctx = parser.ctx_clone();

        let modifiers = parser.parse_modifiers()?;
        let fn_span = parser.expect_keyword(TokenKind::Fn, &ctx)?;
        let start = fn_span.start;
        let name: Option<(String, Span)> = parser.parse_fn_name(&ctx)?;
        let is_anon = name.is_none();
        let path = if let Some((name, span)) = &name {
            let path = ctx.path.append(name);
            parser.mk_node(path, *span)
        } else {
            Node::new(ctx.path.append("<anon>"))
        };

        let ty_params = parser.parse_ty_params(&ctx).recover_seq_with_ctx(
            &mut parser,
            RecoveryCtx::default_seq(Some(&TokenKind::RightParen))
                .with_trailing(TrailingPolicy::Allow)
                .with_newline(false),
            |_| None,
        );
        let (params, param_span) = parse_params(&mut parser)?;
        let mut end = param_span.end;

        // After parameters, aliases are still inside the signature; suppress
        // newline tokens so multi-line arrows/where clauses parse correctly.
        parser = parser.with_newline_mode(NewlineMode::Suppress);
        let ret_ty = if parser.expect_if_operator(TokenKind::Arrow)?.is_some() {
            let t = parser
                .parse_type_annotation(Some(&TokenKind::LeftCurly), &ctx)
                .map(|t| t.into_mono());
            end = t.span().unwrap().end;
            Some(t)
        } else {
            None
        };
        let qualifiers = parser.parse_where_clause(&ctx)?;

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
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let f = &f;
        let ((params, _), spans) =
            self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                let stop_ref = stop.as_ref();
                let seq_ctx = RecoveryCtx::default_seq(stop_ref)
                    .with_trailing(trailing)
                    .with_newline(false);

                parser.parse_sep_seq(&TokenKind::Comma, trailing, stop_ref, ctx, |parser, ctx| {
                    let fault_pos = parser.lex.position();
                    let mut param = f(parser)
                        .map(Some)
                        .recover_seq_with_ctx(parser, seq_ctx.clone(), |parser| {
                            let span = Span {
                                start: fault_pos,
                                end: fault_pos,
                            };
                            let info = Missing::new("parameter", Some(ctx.path.to_string()));
                            let placeholder = Name::new("_");
                            Some(parser.mk_node(FnParam::Missing { info, placeholder }, span))
                        })
                        .unwrap_or_else(|| {
                            let span = Span {
                                start: fault_pos,
                                end: fault_pos,
                            };
                            let info = Missing::new("parameter", Some(ctx.path.to_string()));
                            let placeholder = Name::new("_");
                            parser.mk_node(FnParam::Missing { info, placeholder }, span)
                        });

                    if expect_if!(parser, TokenKind::Equals) {
                        let default = parser.parse_expr(ctx)?;
                        let span = parser
                            .srcmap
                            .span_of(&param)
                            .extend_to(&parser.srcmap.span_of(&default));
                        param = parser.mk_node(
                            FnParam::DefaultValue(Box::new(param), Box::new(default)),
                            span,
                        );
                    }

                    Ok(param)
                })
            })?;

        let (l_span, r_span) = spans.expect("function parameters should have paren spans");
        Ok((
            params,
            Span {
                start: l_span.start,
                end: r_span.end,
            },
        ))
    }
}
