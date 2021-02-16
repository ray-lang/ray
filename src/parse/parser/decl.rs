use super::{
    DeclResult, ExprResult, ParseContext, ParseResult, ParsedDecl, ParsedExpr, Parser, Restrictions,
};

use crate::{
    ast::{
        token::TokenKind, Decl, Decorator, Expr, Extern, HasSource, Impl, Modifier, Name, Node,
        Path, SourceInfo, Struct, Trailing, Trait,
    },
    errors::{RayError, RayErrorKind},
    span::{parsed::Parsed, Pos, Source, Span},
    typing::ty::Ty,
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
    ) -> ParseResult<(Vec<ParsedDecl>, Vec<ParsedDecl>, Vec<ParsedExpr>)> {
        let mut funcs = vec![];
        let mut externs = vec![];
        let mut consts = vec![];
        self.parse_items(
            start,
            Some(TokenKind::RightCurly),
            &ctx,
            |this, kind, doc, decs| match kind {
                TokenKind::Const => {
                    // TODO: should this be wrapped in any way?
                    this.expect_sp(TokenKind::Const)?;
                    let ex = this.parse_expr(ctx)?;
                    let end = this.srcmap.span_of(&ex).end;
                    consts.push(ex);
                    Ok(end)
                }
                TokenKind::Fn | TokenKind::Modifier(_) => {
                    let (mut f, span) = this.parse_fn(only_sigs, ctx)?;
                    let path = f.sig.path.clone();
                    f.sig.doc_comment = doc;
                    f.sig.decorators = decs;
                    let decl = this.mk_decl(Decl::Fn(f), span, path);
                    funcs.push(decl);
                    Ok(span.end)
                }
                TokenKind::Extern => {
                    let start = this.expect_start(TokenKind::Extern)?;
                    let decl = this.parse_extern_fn_sig(start, ctx)?;
                    let end = this.srcmap.span_of(&decl).end;
                    externs.push(decl);
                    Ok(end)
                }
                _ => {
                    let tok = this.token()?;
                    Err(this.unexpected_token(&tok, "a function modifier or signature"))
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
                let path = ctx.path.append(&st.name);
                self.mk_decl(Decl::Struct(st), span, path)
            }
            TokenKind::Impl => {
                let (i, span) = self.parse_impl(false, false, ctx)?;
                self.mk_decl(Decl::Impl(i), span, ctx.path.clone())
            }
            TokenKind::Trait => self.parse_trait(ctx)?,
            TokenKind::Fn | TokenKind::Modifier(_) => {
                let (f, span) = self.parse_fn(false, ctx)?;
                let path = f.sig.path.clone();
                self.mk_decl(Decl::Fn(f), span, path)
            }
            _ => unreachable!(),
        })
    }

    pub(crate) fn parse_extern(&mut self, ctx: &ParseContext) -> DeclResult {
        // extern
        let start = self.expect_start(TokenKind::Extern)?;
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
                let start = self.expect_start(TokenKind::Mut)?;
                let n = self.parse_name_with_type()?;
                let mut span = self.srcmap.span_of(&n);
                span.start = start;
                (Decl::Mutable(n), span)
            }
            _ => {
                let n = self.parse_name_with_type()?;
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
        let decl = match self.must_peek_kind()? {
            TokenKind::Fn | TokenKind::Modifier(_) => {
                let sig = self.parse_fn_sig(ctx)?;
                let span = sig.span;
                let path = sig.path.clone();
                self.mk_decl(Decl::FnSig(sig), span, path)
            }
            _ => {
                let tok = self.token()?;
                return Err(self.unexpected_token(&tok, "a function signature"));
            }
        };

        let end = self.srcmap.span_of(&decl).end;
        Ok(self.mk_decl(
            Decl::Extern(Extern::new(decl)),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_local(&mut self, is_extern: bool, ctx: &ParseContext) -> ExprResult {
        // mut?
        let (is_mut, mut_span) = if peek!(self, TokenKind::Mut) {
            let mut_span = self.expect_sp(TokenKind::Mut)?;
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
            _ => return Err(self.parse_error(format!("expected assign expression"), assign_span)),
        }

        Ok(assign)
    }

    pub(crate) fn parse_trait(&mut self, ctx: &ParseContext) -> DeclResult {
        let start = self.expect_start(TokenKind::Trait)?;
        let (name, span) = self.expect_id()?;
        let mut ctx = ctx.clone();
        ctx.path = ctx.path.append(&name);
        let ty = self.parse_ty_with_name(name, span)?;

        let super_trait = if expect_if!(self, TokenKind::Colon) {
            Some(self.parse_ty()?)
        } else {
            None
        };

        let mut funcs = vec![];
        self.expect(TokenKind::LeftCurly)?;
        loop {
            if peek!(self, TokenKind::RightCurly) {
                break;
            }

            let sig = self.parse_trait_fn_sig(&ctx)?;
            funcs.push(sig);
        }

        let end = self.expect_end(TokenKind::RightCurly)?;

        Ok(self.mk_decl(
            Decl::Trait(Trait {
                ty,
                funcs,
                super_trait,
            }),
            Span { start, end },
            ctx.path,
        ))
    }

    pub(crate) fn parse_struct(&mut self, ctx: &ParseContext) -> ParseResult<(Struct, Span)> {
        let start = self.expect_start(TokenKind::Struct)?;
        let name = self.parse_name_with_type()?;
        let mut end = self.srcmap.span_of(&name).end;

        let ty_params = self.parse_ty_params()?;
        if let Some(ref tp) = ty_params {
            end = tp.rb_span.end;
        }

        let fields = if expect_if!(self, TokenKind::LeftCurly) {
            let f = self.parse_fields()?;
            end = self.expect_end(TokenKind::RightCurly)?;
            Some(f)
        } else {
            None
        };

        Ok((
            Struct {
                name,
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
        let start = self.expect_start(TokenKind::Impl)?;

        let ty = self.parse_ty()?;
        let mut end = ty.span().unwrap().end;

        let qualifiers = self.parse_where_clause()?;

        let (funcs, externs, consts) = if !is_extern {
            let start = self.expect_end(TokenKind::LeftCurly)?;
            let (f, ex, consts) = self.parse_impl_body(start, only_sigs, ctx)?;
            end = self.expect_end(TokenKind::RightCurly)?;
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
            },
            Span { start, end },
        ))
    }

    pub(crate) fn parse_decorators(
        &mut self,
        pos: Pos,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Decorator>, Span)> {
        let mut decs = vec![];
        let mut start = pos;
        let mut end = pos;
        let mut init_pos = false;
        while peek!(self, TokenKind::At) {
            let pos = self.expect_end(TokenKind::At)?;
            if !init_pos {
                start = pos;
                init_pos = true;
            }

            let path = self.parse_path()?;

            let (start_tok, lp_span) = self.expect(TokenKind::LeftParen)?;
            let ps = lp_span.start;
            let mut ctx = ctx.clone();
            ctx.restrictions |= Restrictions::IN_PAREN;
            let args = if !peek!(self, TokenKind::RightParen) {
                let (args, _) = self.parse_name_seq(Trailing::Allow, &ctx)?;
                args
            } else {
                vec![]
            };
            let pe = self.expect_matching(&start_tok, TokenKind::RightParen)?;
            end = pe;

            decs.push(Decorator {
                path,
                args,
                paren_sp: Span { start: ps, end: pe },
            })
        }

        Ok((decs, Span { start, end }))
    }

    pub(crate) fn parse_where_clause(&mut self) -> ParseResult<Vec<Parsed<Ty>>> {
        let mut qualifiers = vec![];
        if !peek!(self, TokenKind::Where) {
            return Ok(qualifiers);
        }

        self.expect(TokenKind::Where)?;

        loop {
            let ty = self.parse_ty()?;
            qualifiers.push(ty);

            if !peek!(self, TokenKind::Comma) {
                break;
            }

            self.expect(TokenKind::Comma)?;
        }

        Ok(qualifiers)
    }

    fn parse_fields(&mut self) -> ParseResult<Vec<Node<Name>>> {
        let mut fields = Vec::new();
        loop {
            if !peek!(self, TokenKind::Identifier { .. }) {
                break;
            }
            let n = self.parse_name_with_type()?;
            let end = self.srcmap.span_of(&n).end;
            fields.push(n);

            let next_comma = expect_if!(self, TokenKind::Comma);
            if !self.is_eol() && !next_comma {
                return Err(RayError {
                    msg: format!("{}", "fields must be separated by a newline or comma"),
                    src: vec![Source::new(
                        self.options.filepath.clone(),
                        Span { start: end, end },
                        Path::new(),
                    )],
                    kind: RayErrorKind::Parse,
                });
            }
        }
        Ok(fields)
    }
}
