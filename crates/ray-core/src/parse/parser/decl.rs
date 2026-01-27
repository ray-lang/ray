use std::ops::Deref;

use itertools::Itertools;
use ray_shared::{
    def::{DefHeader, DefId, DefKind},
    span::{Pos, Span, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::NominalKind;

use crate::{
    ast::{
        Assign, Decl, Decorator, Expr, Extern, Func, Impl, Modifier, Name, Node, Pattern, Struct,
        TrailingPolicy, Trait, TraitDirective, TraitDirectiveKind, token::TokenKind,
    },
    errors::{RayError, RayErrorKind},
    parse::lexer::NewlineMode,
    sourcemap::TriviaKind,
};

use super::{
    DeclResult, ExprResult, ParseResult, ParsedDecl, Parser, Recover, RecoveryCtx, Restrictions,
    context::{ParseContext, SeqSpec},
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
        impl_def_id: DefId,
        start: Pos,
        only_sigs: bool,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Node<Decl>>, Vec<ParsedDecl>, Vec<Node<Assign>>)> {
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
            |parser, kind, doc, _| match kind {
                TokenKind::Const => parser.enter_def::<ParseResult<Pos>>(|parser, def_id| {
                    parser.expect_keyword(TokenKind::Const, ctx)?;
                    let ex = parser.parse_expr(ctx)?;
                    let span = parser.srcmap.span_of(&ex);
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
                                parser.parse_error(
                                    format!(
                                        "expected a constant assignment expression, but found {}",
                                        ex_desc,
                                    ),
                                    span,
                                    ctx,
                                )
                            })
                    })?;

                    let name = assign_node.lhs.get_name().unwrap();
                    let name_span = parser.srcmap.span_of(&assign_node.lhs);
                    let annotated = assign_node.is_annotated();
                    parser.defs.push(DefHeader {
                        def_id,
                        root_node: assign_node.lhs.id,
                        name,
                        kind: DefKind::AssociatedConst { annotated },
                        span,
                        name_span,
                        parent: Some(impl_def_id),
                    });

                    let end = parser.srcmap.span_of(&assign_node).end;
                    consts.push(assign_node);
                    Ok(end)
                }),
                TokenKind::Fn | TokenKind::Modifier(_) => {
                    parser.enter_def::<ParseResult<Pos>>(|parser, def_id| {
                        let (mut f, span) = parser.parse_fn(only_sigs, ctx)?;
                        f.sig.doc_comment = doc;
                        f.sig.is_method = true;
                        let name = f.sig.path.to_short_name();
                        let name_span = parser.srcmap.get(&f.sig.path).span.unwrap();
                        // Wrap in Decl::Func so methods have the same shape as top-level functions
                        let decl_node = parser.mk_node(Decl::Func(f), span, ctx.path.clone());
                        parser.defs.push(DefHeader {
                            def_id,
                            root_node: decl_node.id,
                            name,
                            kind: DefKind::Method,
                            span,
                            name_span,
                            parent: Some(impl_def_id),
                        });
                        funcs.push(decl_node);
                        Ok(span.end)
                    })
                }
                TokenKind::Extern => {
                    let extern_span = parser.expect_keyword(TokenKind::Extern, ctx)?;
                    let start = extern_span.start;
                    let decl = parser.parse_extern_fn_sig(start, Some(impl_def_id), ctx)?;
                    let end = parser.srcmap.span_of(&decl).end;
                    externs.push(decl);
                    Ok(end)
                }
                _ => {
                    let tok = parser.token()?;
                    Err(parser.unexpected_token(&tok, "a function modifier or signature", ctx))
                }
            },
        )?;
        Ok((funcs, externs, consts))
    }

    pub(crate) fn parse_decl(&mut self, kind: &TokenKind, ctx: &ParseContext) -> DeclResult {
        match kind {
            TokenKind::Extern => self.parse_extern(ctx),
            TokenKind::Struct => self.parse_struct(ctx),
            TokenKind::Impl => self.parse_impl(false, false, ctx),
            TokenKind::Trait => self.parse_trait(ctx),
            TokenKind::Fn | TokenKind::Modifier(_) => {
                self.enter_def::<DeclResult>(|parser, def_id| {
                    let (f, span) = parser.parse_fn(false, ctx)?;
                    let name = f.sig.path.to_short_name();
                    let name_span = parser.srcmap.get(&f.sig.path).span.unwrap();
                    let signature = f.to_sig_status();
                    let node = parser.mk_decl(Decl::Func(f), span, ctx.path.clone());
                    parser.defs.push(DefHeader {
                        def_id,
                        root_node: node.id,
                        name,
                        kind: DefKind::Function { signature },
                        span,
                        name_span,
                        parent: None,
                    });
                    Ok(node)
                })
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn parse_extern(&mut self, ctx: &ParseContext) -> DeclResult {
        // extern
        let extern_span = self.expect_keyword(TokenKind::Extern, ctx)?;
        let start = extern_span.start;
        // parse_extern_fn_sig already wraps in Extern, so return directly
        if matches!(
            self.must_peek_kind()?,
            TokenKind::Fn | TokenKind::Modifier(_)
        ) {
            return self.parse_extern_fn_sig(start, None, ctx);
        }
        let decl = match self.must_peek_kind()? {
            TokenKind::Struct => self.parse_struct(ctx)?,
            TokenKind::Impl => self.parse_impl(true, true, ctx)?,
            _ => self.enter_def::<DeclResult>(|parser, def_id| {
                let (mutable, mut_span) = if matches!(parser.must_peek_kind()?, TokenKind::Mut) {
                    (true, Some(parser.expect_keyword(TokenKind::Mut, ctx)?))
                } else {
                    (false, None)
                };

                let name_node = parser.parse_name_with_type(None, ctx)?;
                let name = name_node.path.to_short_name();
                let name_span = parser.srcmap.span_of(&name_node);
                let mut span = name_span;
                if let Some(mut_span) = mut_span {
                    span.start = mut_span.start;
                }

                let annotated = name_node.ty.is_some();
                let decl = if mutable {
                    parser.mk_decl(Decl::Mutable(name_node), span, ctx.path.clone())
                } else {
                    parser.mk_decl(Decl::Name(name_node), span, ctx.path.clone())
                };

                parser.defs.push(DefHeader {
                    def_id,
                    root_node: decl.id,
                    name,
                    kind: DefKind::Binding { annotated, mutable },
                    span,
                    name_span,
                    parent: None,
                });

                Ok(decl)
            })?,
        };
        let decl_span = self.srcmap.get(&decl).span.unwrap();
        Ok(self.mk_decl(
            Decl::Extern(Extern::new(decl)),
            Span {
                start,
                end: decl_span.end,
            },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_extern_fn_sig(
        &mut self,
        start: Pos,
        parent_def_id: Option<DefId>,
        ctx: &ParseContext,
    ) -> DeclResult {
        let parser = &mut self.with_scope(ctx).with_description("parse extern fn sig");
        let ctx = &parser.ctx_clone();

        let decl = match parser.must_peek_kind()? {
            TokenKind::Fn | TokenKind::Modifier(_) => {
                parser.enter_def::<DeclResult>(|parser, def_id| {
                    let sig = parser.parse_fn_sig(ctx)?;
                    let span = sig.span;
                    let path = sig.path.value.clone();

                    let name = path.to_short_name();
                    let name_span = parser.srcmap.get(&sig.path).span.unwrap();

                    let node = parser.mk_decl(Decl::FnSig(sig), span, path);
                    parser.defs.push(DefHeader {
                        def_id,
                        root_node: node.id,
                        name,
                        kind: DefKind::Method,
                        span,
                        name_span,
                        parent: parent_def_id,
                    });
                    Ok(node)
                })?
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
        self.enter_def::<DeclResult>(|parser, trait_def_id| {
            let trait_span = parser.expect_keyword(TokenKind::Trait, ctx)?;
            let start = trait_span.start;
            let (name, name_span) = parser.expect_id(ctx)?;

            let raw_path = ctx.path.append(&name);
            let path = parser.mk_node(raw_path, name_span, ctx.path.clone());

            let parser = &mut parser
                .with_scope(&ctx)
                .with_path(path.value.clone())
                .with_description("parsing trait declaration");
            let ctx = &parser.ctx_clone();

            let ty = parser
                .parse_ty_with_name(name.clone(), name_span, &ctx)
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

                    parser.enter_def::<ParseResult<()>>(|parser, def_id| {
                        let sig = parser.parse_trait_fn_sig(&ctx)?;
                        let span = sig.span;
                        let name = sig.path.to_short_name();
                        let name_span = parser.srcmap.get(&sig.path).span.unwrap();
                        let node = parser.mk_decl(Decl::FnSig(sig), span, ctx.path.clone());
                        parser.defs.push(DefHeader {
                            def_id,
                            root_node: node.id,
                            name,
                            kind: DefKind::Method,
                            span,
                            name_span,
                            parent: Some(trait_def_id),
                        });
                        fields.push(node);
                        Ok(())
                    })?
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

            let tr = Trait {
                path,
                ty,
                fields,
                super_trait,
                directives,
            };

            let scope_path = tr.path.value.clone();
            let span = Span { start, end };
            let node = parser.mk_decl(Decl::Trait(tr), span, scope_path);
            parser.defs.push(DefHeader {
                def_id: trait_def_id,
                root_node: node.id,
                name,
                kind: DefKind::Trait,
                span,
                name_span,
                parent: None,
            });

            Ok(node)
        })
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

    pub(crate) fn parse_struct(&mut self, ctx: &ParseContext) -> DeclResult {
        self.enter_def(|parser, def_id| {
            let keyword_kinds = &[TokenKind::Struct];
            let Some(kw) = parser.expect_one_of(keyword_kinds, Some(TriviaKind::Keyword), ctx)?
            else {
                let tok = parser.token()?;
                let expected = keyword_kinds.iter().map(TokenKind::to_string).join(" or ");
                return Err(parser.unexpected_token(&tok, &expected, ctx));
            };

            let kind = match kw.kind {
                TokenKind::Struct => NominalKind::Struct,
                _ => unreachable!("expected nominal kind token"),
            };

            let start = kw.span.start;

            // parse name of struct
            let (name, name_span) = parser.expect_id(ctx)?;
            let raw_path = ctx.path.append(&name);
            let path = parser.mk_node(raw_path, name_span, ctx.path.clone());

            let mut end = name_span.end;

            let ty_params = parser.parse_ty_params(ctx)?;
            if let Some(ref tp) = ty_params {
                end = tp.rb_span.end;
            }

            let fields = if peek!(parser, TokenKind::LeftCurly) {
                parser.expect(TokenKind::LeftCurly, ctx)?;
                parser.consume_newlines(ctx)?;
                let f = parser.parse_fields(ctx)?;
                end = parser.expect_end(TokenKind::RightCurly, ctx)?;
                Some(f)
            } else {
                None
            };

            let node_path = ctx.path.append(&path);
            let st = Struct {
                kind,
                path,
                ty_params,
                fields,
            };

            let span = Span { start, end };
            let node = parser.mk_decl(Decl::Struct(st), span, node_path);
            parser.defs.push(DefHeader {
                def_id,
                root_node: node.id,
                kind: DefKind::Struct,
                span,
                name,
                name_span,
                parent: None,
            });
            Ok(node)
        })
    }

    pub(crate) fn parse_impl(
        &mut self,
        only_sigs: bool,
        is_extern: bool,
        ctx: &ParseContext,
    ) -> DeclResult {
        self.enter_def(|parser, impl_def_id| {
            let impl_span = parser.expect_keyword(TokenKind::Impl, ctx)?;
            let start = impl_span.start;

            let is_object = if peek!(parser, TokenKind::Object) {
                parser.expect_keyword(TokenKind::Object, ctx)?;
                true
            } else {
                false
            };

            let ty = parser
                .parse_type_annotation(Some(&TokenKind::LeftCurly), ctx)
                .map(|t| t.into_mono());
            let mut end = ty.span().unwrap().end;

            let qualifiers = parser.parse_where_clause(ctx)?;

            let (funcs, externs, consts) = if !is_extern {
                let impl_path = if !is_object {
                    ty.type_argument_at(0).unwrap_or(&Ty::Never).get_path()
                } else {
                    ty.get_path()
                };
                let mut ctx = ctx.clone();
                log::debug!(
                    "[parse_impl] base ctx.path = {}, impl_ty = {}",
                    ctx.path,
                    impl_path
                );
                ctx.path = ctx.path.append_path(impl_path);
                log::debug!("[parse_impl] appended ctx.path = {}", ctx.path);
                let start = parser.expect_end(TokenKind::LeftCurly, &ctx)?;
                let (f, ex, consts) =
                    parser.parse_impl_body(impl_def_id, start, only_sigs, &ctx)?;
                end = parser.expect_end(TokenKind::RightCurly, &ctx)?;
                (Some(f), Some(ex), Some(consts))
            } else {
                (None, None, None)
            };

            let imp = Impl {
                ty,
                qualifiers,
                funcs,
                externs,
                consts,
                is_object,
            };

            let span = Span { start, end };
            let name = imp.ty.get_path().with_names_only().to_short_name();
            let name_span = *imp.ty.span().unwrap();
            let node = parser.mk_decl(Decl::Impl(imp), span, ctx.path.clone());
            parser.defs.push(DefHeader {
                def_id: impl_def_id,
                root_node: node.id,
                name,
                kind: DefKind::Impl,
                span,
                name_span,
                parent: None,
            });
            Ok(node)
        })
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
