use std::ops::Deref;

use itertools::Itertools;

use super::{
    DeclResult, ExprResult, ParseResult, ParsedDecl, Parser, Recover, RecoveryCtx, Restrictions,
    context::{ParseContext, SeqSpec},
};

use crate::{
    ast::{
        Assign, Decl, Decorator, Expr, Extern, Func, Impl, Modifier, Name, Node, Pattern, Struct,
        TrailingPolicy, Trait, TraitDirective, TraitDirectiveKind, token::TokenKind,
    },
    errors::{RayError, RayErrorKind},
    parse::lexer::NewlineMode,
    span::{Pos, Span, TriviaKind, parsed::Parsed},
    typing::ty::{NominalKind, Ty},
};

impl Parser<'_> {
    pub(crate) fn parse_modifiers(&mut self) -> ParseResult<Vec<Modifier>> {
        let mut modifiers = vec![];
        loop {
            match self.peek_kind() {
                TokenKind::Modifier(m) => {
                    self.token()?;
                    modifiers.push(m);
                }
                _ => break,
            }
        }
        Ok(modifiers)
    }

    pub(crate) fn parse_impl_body(
        &mut self,
        start: Pos,
        only_sigs: bool,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Node<Func>>, Vec<ParsedDecl>, Vec<Node<Assign>>)> {
        let mut funcs = vec![];
        let mut externs = vec![];
        let mut consts = vec![];

        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse impl body")
            .with_newline_mode(NewlineMode::Emit);
        let ctx = &parser.ctx_clone();

        parser.parse_items(
            start,
            Some(TokenKind::RightCurly),
            &ctx,
            |this, kind, doc, _| match kind {
                TokenKind::Const => {
                    this.expect_keyword(TokenKind::Const, ctx)?;
                    let ex = this.parse_expr(ctx)?;
                    let span = this.srcmap.span_of(&ex);
                    let ex_desc = ex.desc().to_string();
                    let assign_node = ex.try_take_map(|ex| {
                        maybe_variant!(ex, if Expr::Assign(a))
                            .and_then(|assign| {
                                if matches!(assign.lhs.deref(), Pattern::Name(_)) {
                                    Some(assign)
                                } else {
                                    None
                                }
                            })
                            .ok_or_else(|| {
                                this.parse_error(
                                    format!(
                                        "expected a constant assignment expression, but found {}",
                                        ex_desc,
                                    ),
                                    span,
                                    ctx,
                                )
                            })
                    })?;

                    let end = this.srcmap.span_of(&assign_node).end;
                    consts.push(assign_node);
                    Ok(end)
                }
                TokenKind::Fn | TokenKind::Modifier(_) => {
                    let (mut f, span) = this.parse_fn(only_sigs, ctx)?;
                    f.sig.doc_comment = doc;
                    f.sig.is_method = true;
                    let func_node = this.mk_node_with_path(f, span, ctx.path.clone());
                    funcs.push(func_node);
                    Ok(span.end)
                }
                TokenKind::Extern => {
                    let extern_span = this.expect_keyword(TokenKind::Extern, ctx)?;
                    let start = extern_span.start;
                    let decl = this.parse_extern_fn_sig(start, ctx)?;
                    let end = this.srcmap.span_of(&decl).end;
                    externs.push(decl);
                    Ok(end)
                }
                _ => {
                    let tok = this.token()?;
                    Err(this.unexpected_token(&tok, "a function modifier or signature", ctx))
                }
            },
        )?;
        Ok((funcs, externs, consts))
    }

    pub(crate) fn parse_decl(&mut self, kind: &TokenKind, ctx: &ParseContext) -> DeclResult {
        Ok(match kind {
            TokenKind::Extern => self.parse_extern(ctx)?,
            TokenKind::Struct => {
                let (st, span) = self.parse_struct(ctx)?;
                let path = ctx.path.append(&st.path);
                self.mk_decl(Decl::Struct(st), span, path)
            }
            TokenKind::Impl => {
                let (i, span) = self.parse_impl(false, false, ctx)?;
                self.mk_decl(Decl::Impl(i), span, ctx.path.clone())
            }
            TokenKind::Trait => self.parse_trait(ctx)?,
            TokenKind::Fn | TokenKind::Modifier(_) => {
                let (f, span) = self.parse_fn(false, ctx)?;
                self.mk_decl(Decl::Func(f), span, ctx.path.clone())
            }
            _ => unreachable!(),
        })
    }

    pub(crate) fn parse_extern(&mut self, ctx: &ParseContext) -> DeclResult {
        // extern
        let extern_span = self.expect_keyword(TokenKind::Extern, ctx)?;
        let start = extern_span.start;
        let (kind, span) = match self.must_peek_kind()? {
            TokenKind::Struct => {
                let (st, span) = self.parse_struct(ctx)?;
                (Decl::Struct(st), span)
            }
            TokenKind::Impl => {
                let (imp, span) = self.parse_impl(true, true, ctx)?;
                (Decl::Impl(imp), span)
            }
            TokenKind::Fn | TokenKind::Modifier(_) => return self.parse_extern_fn_sig(start, ctx),
            TokenKind::Mut => {
                let mut_span = self.expect_keyword(TokenKind::Mut, ctx)?;
                let n = self.parse_name_with_type(None, ctx)?;
                let mut span = self.srcmap.span_of(&n);
                span.start = mut_span.start;
                (Decl::Mutable(n), span)
            }
            _ => {
                let n = self.parse_name_with_type(None, ctx)?;
                let span = self.srcmap.span_of(&n);
                (Decl::Name(n), span)
            }
        };

        let decl = self.mk_decl(kind, span, ctx.path.clone());
        Ok(self.mk_decl(
            Decl::Extern(Extern::new(decl)),
            Span {
                start,
                end: span.end,
            },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_extern_fn_sig(&mut self, start: Pos, ctx: &ParseContext) -> DeclResult {
        let parser = &mut self.with_scope(ctx).with_description("parse extern fn sig");
        let ctx = &parser.ctx_clone();

        let decl = match parser.must_peek_kind()? {
            TokenKind::Fn | TokenKind::Modifier(_) => {
                let sig = parser.parse_fn_sig(ctx)?;
                let span = sig.span;
                let path = sig.path.value.clone();
                parser.mk_decl(Decl::FnSig(sig), span, path)
            }
            _ => {
                let tok = parser.token()?;
                return Err(parser.unexpected_token(&tok, "a function signature", ctx));
            }
        };

        let end = parser.srcmap.span_of(&decl).end;
        Ok(parser.mk_decl(
            Decl::Extern(Extern::new(decl)),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_local(&mut self, is_extern: bool, ctx: &ParseContext) -> ExprResult {
        // mut?
        let (is_mut, mut_span) = if peek!(self, TokenKind::Mut) {
            let mut_span = self.expect_keyword(TokenKind::Mut, ctx)?;
            (true, Some(mut_span))
        } else {
            (false, None)
        };

        let mut assign = self.parse_expr(&ctx)?;
        let mut assign_span = self.srcmap.span_of(&assign);
        if let Some(mut_span) = mut_span {
            assign_span.start = mut_span.start;
            self.srcmap.respan(&assign, assign_span);
        }

        if is_extern {
            return Ok(assign);
        }

        match &mut assign.value {
            Expr::Assign(a) => {
                a.is_mut = is_mut;
                a.mut_span = mut_span;
            }
            _ => {
                return Err(self.parse_error(
                    "expected assign expression".to_string(),
                    assign_span,
                    ctx,
                ));
            }
        }

        Ok(assign)
    }

    pub(crate) fn parse_trait(&mut self, ctx: &ParseContext) -> DeclResult {
        let trait_span = self.expect_keyword(TokenKind::Trait, ctx)?;
        let start = trait_span.start;
        let (name_str, name_span) = self.expect_id(ctx)?;

        let raw_path = ctx.path.append(&name_str);
        let path = self.mk_node(raw_path, name_span);

        let parser = &mut self
            .with_scope(&ctx)
            .with_path(path.value.clone())
            .with_description("parsing trait declaration");
        let ctx = &parser.ctx_clone();

        let ty = parser
            .parse_ty_with_name(name_str, name_span, &ctx)
            .recover_with_ctx(
                parser,
                RecoveryCtx::expr(Some(&TokenKind::LeftCurly)).with_ternary_sensitive(false),
                |parser, recovered| parser.missing_type(name_span.start, recovered),
            )
            .map(|t| t.into_mono());

        let super_trait = if expect_if!(parser, TokenKind::Colon) {
            Some(
                parser
                    .parse_type_annotation(Some(&TokenKind::LeftCurly), &ctx)
                    .map(|t| t.into_mono()),
            )
        } else {
            None
        };

        let mut fields = vec![];
        let mut directives = vec![];

        let parser = &mut parser
            .with_scope(&ctx)
            .with_description("parse trait fields");
        let ctx = &parser.ctx_clone();

        (|| {
            parser.expect(TokenKind::LeftCurly, &ctx)?;
            parser.consume_newlines(ctx)?;

            parser.parse_trait_directives(&mut directives, ctx)?;

            loop {
                parser.consume_newlines(ctx)?;
                if peek!(parser, TokenKind::RightCurly) {
                    break;
                }

                let sig = parser.parse_trait_fn_sig(&ctx)?;
                let span = sig.span;
                fields.push(parser.mk_decl(Decl::FnSig(sig), span, ctx.path.clone()));
            }

            Ok(())
        })()
        .recover_with_ctx(
            parser,
            RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                .with_newline(true)
                .with_decl_stops(false),
            |_, _| (),
        );

        let end = parser.expect_end(TokenKind::RightCurly, &ctx)?;

        let scope_path = parser.ctx().path.clone();
        Ok(parser.mk_decl(
            Decl::Trait(Trait {
                path,
                ty,
                fields,
                super_trait,
                directives,
            }),
            Span { start, end },
            scope_path,
        ))
    }

    fn parse_trait_directives(
        &mut self,
        directives: &mut Vec<Parsed<TraitDirective>>,
        ctx: &ParseContext,
    ) -> ParseResult<()> {
        self.consume_newlines(ctx)?;

        while peek!(self, TokenKind::Default) {
            let default_span = self.expect_keyword(TokenKind::Default, ctx)?;
            let start = default_span.start;
            let spec = SeqSpec {
                delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
                trailing: TrailingPolicy::Forbid,
                newline: NewlineMode::Suppress,
                restrictions: Restrictions::IN_PAREN,
            };

            let ((args, _), spans) =
                self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                    parser.parse_sep_seq(
                        &TokenKind::Comma,
                        trailing,
                        stop.as_ref(),
                        ctx,
                        |parser, ctx| {
                            Ok(parser
                                .parse_type_annotation(stop.as_ref(), ctx)
                                .map(|t| t.into_mono()))
                        },
                    )
                })?;

            let end = spans.map(|(_, right)| right.end).unwrap_or(start);

            directives.push(Parsed::new(
                TraitDirective {
                    kind: TraitDirectiveKind::Default,
                    args,
                },
                self.mk_src(Span { start, end }),
            ));

            // Allow blank lines between directives without looping on them.
            self.consume_newlines(ctx)?;
        }

        Ok(())
    }

    pub(crate) fn parse_struct(&mut self, ctx: &ParseContext) -> ParseResult<(Struct, Span)> {
        let keyword_kinds = &[TokenKind::Struct];
        let Some(kw) = self.expect_one_of(keyword_kinds, Some(TriviaKind::Keyword), ctx)? else {
            let tok = self.token()?;
            let expected = keyword_kinds.iter().map(TokenKind::to_string).join(" or ");
            return Err(self.unexpected_token(&tok, &expected, ctx));
        };

        let kind = match kw.kind {
            TokenKind::Struct => NominalKind::Struct,
            _ => unreachable!("expected nominal kind token"),
        };

        let start = kw.span.start;

        // parse name of struct
        let (name_str, name_span) = self.expect_id(ctx)?;
        let raw_path = ctx.path.append(&name_str);
        let path = self.mk_node(raw_path, name_span);

        let mut end = name_span.end;

        let ty_params = self.parse_ty_params(ctx)?;
        if let Some(ref tp) = ty_params {
            end = tp.rb_span.end;
        }

        let fields = if peek!(self, TokenKind::LeftCurly) {
            self.expect(TokenKind::LeftCurly, ctx)?;
            self.consume_newlines(ctx)?;
            let f = self.parse_fields(ctx)?;
            end = self.expect_end(TokenKind::RightCurly, ctx)?;
            Some(f)
        } else {
            None
        };

        Ok((
            Struct {
                kind,
                path,
                ty_params,
                fields,
            },
            Span { start, end },
        ))
    }

    pub(crate) fn parse_impl(
        &mut self,
        only_sigs: bool,
        is_extern: bool,
        ctx: &ParseContext,
    ) -> ParseResult<(Impl, Span)> {
        let impl_span = self.expect_keyword(TokenKind::Impl, ctx)?;
        let start = impl_span.start;

        let is_object = if peek!(self, TokenKind::Object) {
            self.expect_keyword(TokenKind::Object, ctx)?;
            true
        } else {
            false
        };

        let ty = self
            .parse_type_annotation(Some(&TokenKind::LeftCurly), ctx)
            .map(|t| t.into_mono());
        let mut end = ty.span().unwrap().end;

        let qualifiers = self.parse_where_clause(ctx)?;

        let (funcs, externs, consts) = if !is_extern {
            let impl_ty = ty.get_ty_param_at(0).get_path();
            let mut ctx = ctx.clone();
            ctx.path = ctx.path.append_path(impl_ty);
            let start = self.expect_end(TokenKind::LeftCurly, &ctx)?;
            let (f, ex, consts) = self.parse_impl_body(start, only_sigs, &ctx)?;
            end = self.expect_end(TokenKind::RightCurly, &ctx)?;
            (Some(f), Some(ex), Some(consts))
        } else {
            (None, None, None)
        };

        Ok((
            Impl {
                ty,
                qualifiers,
                funcs,
                externs,
                consts,
                is_object,
            },
            Span { start, end },
        ))
    }

    pub(crate) fn parse_decorators(
        &mut self,
        pos: Pos,
        ctx: &ParseContext,
    ) -> ParseResult<(Option<Vec<Decorator>>, Span)> {
        log::debug!("[parse_decorators] pos={:?}", pos);
        let mut decs = None;
        let start = pos;
        let mut end = pos;
        while peek!(self, TokenKind::At) {
            let _: Pos = self.expect_end(TokenKind::At, ctx)?;
            let path = self.parse_path(ctx)?;
            end = self.srcmap.get(&path).span.unwrap().end;
            log::debug!("[parse_decorators] path={:?}", path);

            let (args, paren_sp) = if peek!(self, TokenKind::LeftParen) {
                let spec = SeqSpec {
                    delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
                    trailing: TrailingPolicy::Allow,
                    newline: NewlineMode::Suppress,
                    restrictions: Restrictions::IN_PAREN,
                };

                let ((args, _trailing), spans) =
                    self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                        parser.parse_sep_seq(
                            &TokenKind::Comma,
                            trailing,
                            stop.as_ref(),
                            ctx,
                            |parser, ctx| parser.parse_name_with_type(stop.as_ref(), ctx),
                        )
                    })?;

                let (l_span, r_span) = spans.expect("decorator args should have paren spans");
                end = r_span.end;
                (
                    args,
                    Some(Span {
                        start: l_span.start,
                        end: r_span.end,
                    }),
                )
            } else {
                log::debug!("[parse_decorators] no parameters");
                (vec![], None)
            };

            if decs.is_none() {
                decs = Some(vec![]);
            }

            if let Some(decs) = decs.as_mut() {
                decs.push(Decorator {
                    path,
                    args,
                    paren_sp,
                })
            }
        }

        log::debug!(
            "[parse_decorators] start={:?}, end={:?}, decs={:?}",
            start,
            end,
            decs
        );
        Ok((decs, Span { start, end }))
    }

    pub(crate) fn parse_where_clause(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Vec<Parsed<Ty>>> {
        let mut parser = self.with_scope(ctx).with_description("parse where clause");
        let ctx = &parser.ctx_clone();

        let mut qualifiers = vec![];
        if !peek!(parser, TokenKind::Where) {
            return Ok(qualifiers);
        }

        let has_where = parser
            .expect_keyword(TokenKind::Where, ctx)
            .map(|_| Some(()))
            .recover_seq_with_ctx(
                &mut parser,
                RecoveryCtx::default_seq(None)
                    .with_trailing(TrailingPolicy::Allow)
                    .with_newline(false),
                |_| None,
            );
        if has_where.is_none() {
            return Ok(qualifiers);
        }

        parser = parser.with_newline_mode(NewlineMode::Suppress);
        let (tys, _) = parser.parse_sep_seq(
            &TokenKind::Comma,
            TrailingPolicy::Allow,
            None,
            ctx,
            |parser, ctx| {
                Ok(parser
                    .parse_type_annotation(Some(&TokenKind::Comma), ctx)
                    .map(|t| t.into_mono()))
            },
        )?;
        qualifiers.extend(tys);

        Ok(qualifiers)
    }

    fn parse_fields(&mut self, ctx: &ParseContext) -> ParseResult<Vec<Node<Name>>> {
        let mut fields = Vec::new();
        loop {
            self.consume_newlines(ctx)?;
            if !peek!(self, TokenKind::Identifier { .. }) {
                break;
            }

            let field = self
                .parse_name_with_type(Some(&TokenKind::RightCurly), ctx)
                .map(Some)
                .recover_with_ctx(
                    self,
                    RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                        .with_newline(true)
                        .with_decl_stops(false),
                    |_, _| None,
                );

            match field {
                Some(n) => {
                    let end = self.srcmap.span_of(&n).end;
                    fields.push(n);

                    let next_comma = peek!(self, TokenKind::Comma);
                    if !self.is_eol() && !next_comma && !peek!(self, TokenKind::RightCurly) {
                        Result::<(), RayError>::Err(RayError {
                            msg: "fields must be separated by a newline or comma".to_string(),
                            src: vec![self.mk_src(Span { start: end, end })],
                            kind: RayErrorKind::Parse,
                            context: Some("struct field parsing".to_string()),
                        })
                        .recover_with_ctx(
                            self,
                            RecoveryCtx::stmt(Some(&TokenKind::RightCurly))
                                .with_newline(true)
                                .with_decl_stops(false),
                            |_, _| (),
                        );
                    }

                    if next_comma {
                        // consume it
                        let _ = self.token();
                    }

                    if peek!(self, TokenKind::RightCurly) || self.is_eof() {
                        break;
                    }
                }
                None => {
                    if peek!(self, TokenKind::RightCurly) || self.is_eof() {
                        break;
                    } else {
                        continue;
                    }
                }
            }
        }
        Ok(fields)
    }
}
