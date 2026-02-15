use ray_shared::{
    pathlib::Path,
    span::{Span, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::TyScheme;

use crate::{
    ast::{TrailingPolicy, TypeParams, token::TokenKind},
    parse::{
        ParseContext, ParseResult, Parser,
        lexer::NewlineMode,
        parser::{Restrictions, context::SeqSpec},
    },
};

use super::{Recover, RecoveryCtx};

impl Parser<'_> {
    pub(crate) fn parse_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        self.parse_ty_with(None, ctx)
    }

    fn parse_ty_with(
        &mut self,
        ty: Option<Parsed<TyScheme>>,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        let ty = if let Some(ty) = ty {
            ty
        } else {
            self.parse_ty_base(None, ctx)?
        };

        self.parse_nilable_ty(ty, ctx)
    }

    fn parse_nilable_ty(
        &mut self,
        ty: Parsed<TyScheme>,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        Ok(if peek!(self, TokenKind::Question) {
            let (ty, src, mut ids) = ty.take();
            let start = src.span.unwrap().start;
            let end = self.expect_end(TokenKind::Question, ctx)?;
            let span = Span { start, end };

            // Add a synthetic ID for the nilable wrapper type (Ty::Proj("nilable", [...])).
            // This is needed because Ty::flatten() includes the Proj type itself plus its
            // type parameters, so the synthetic IDs must match.
            let nilable_synth_id = self.mk_synthetic(span);
            ids.insert(0, nilable_synth_id);

            let mut parsed = Parsed::new(
                TyScheme::from_mono(Ty::nilable(ty.into_mono())),
                self.mk_src(span),
            );
            parsed.set_synthetic_ids(ids);
            parsed
        } else {
            ty
        })
    }

    pub(crate) fn parse_ty_params(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Option<TypeParams>> {
        if !peek!(self, TokenKind::LeftBracket) {
            Ok(None)
        } else {
            let spec = SeqSpec {
                delimiters: Some((TokenKind::LeftBracket, TokenKind::RightBracket)),
                trailing: TrailingPolicy::Allow,
                newline: NewlineMode::Suppress,
                restrictions: Restrictions::IN_PAREN,
            };

            let ((tys, _trailing), spans) =
                self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                    let stop_ref = stop.as_ref();
                    parser.parse_sep_seq(
                        &TokenKind::Comma,
                        trailing,
                        stop_ref,
                        ctx,
                        |parser, ctx| {
                            Ok(parser
                                .parse_type_annotation(stop_ref, ctx)
                                .map(|ty| ty.into_mono()))
                        },
                    )
                })?;

            let (lb, rb) = spans.expect("type parameters should return spans");
            Ok(Some(TypeParams {
                tys,
                lb_span: lb,
                rb_span: rb,
            }))
        }
    }

    fn parse_ty_complex(&mut self, ctx: &ParseContext) -> ParseResult<Option<Parsed<TyScheme>>> {
        Ok(if peek!(self, TokenKind::Asterisk) {
            Some(self.parse_ptr_ty(ctx)?)
        } else if peek!(self, TokenKind::UpperFn) {
            Some(self.parse_fn_ty(ctx)?)
        } else if peek!(self, TokenKind::LeftBracket) {
            Some(self.parse_arr_ty(ctx)?)
        } else if peek!(self, TokenKind::SingleQuote) {
            Some(self.parse_generic_ty(ctx)?)
        } else if peek!(self, TokenKind::LeftParen) {
            Some(self.parse_tuple_ty(ctx)?)
        } else {
            None
        })
    }

    fn parse_ty_base(
        &mut self,
        ident: Option<(String, Span)>,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        if let Some(t) = self.parse_ty_complex(ctx)? {
            Ok(t)
        } else {
            let (name, span) = if let Some((name, span)) = ident {
                (name, span)
            } else {
                self.expect_id(ctx)?
            };
            let path = if expect_if!(self, TokenKind::DoubleColon) {
                self.parse_path_with((name, span), ctx)?
            } else {
                self.mk_node(Path::from(vec![name]), span, ctx.path.clone())
            };
            let span = self.srcmap.span_of(&path);
            self.parse_ty_with_path(path.value, span, ctx)
        }
    }

    fn parse_ptr_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let start = self.expect_start(TokenKind::Asterisk, ctx)?;
        let ptee_ty = self.parse_type_annotation(None, ctx);
        let (ptee_ty, ptee_src, ids) = ptee_ty.take();
        let end = ptee_src.span.unwrap().end;
        let mut parsed = Parsed::new(
            TyScheme::from_mono(Ty::ref_of(ptee_ty.into_mono())),
            self.mk_src(Span { start, end }),
        );
        parsed.set_synthetic_ids(ids);
        Ok(parsed)
    }

    fn parse_arr_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftBracket, TokenKind::RightBracket)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let (result, spans) = self.parse_delimited_seq(spec, ctx, |parser, _, _, ctx| {
            // stop is always Some(RightBracket)
            let start = parser.lex.position();
            let el_ty = parser.parse_type_annotation(Some(&TokenKind::Semi), ctx);
            parser.expect(TokenKind::Semi, ctx)?;
            Ok(match parser.parse_arr_ty_size(ctx) {
                Ok(size) => Ok((el_ty, size)),
                Err(err) => {
                    let placeholder = Err(err).recover_with_ctx(
                        parser,
                        RecoveryCtx::expr(Some(&TokenKind::RightBracket))
                            .with_ternary_sensitive(false),
                        |parser, recovered| parser.missing_type(start, recovered),
                    );
                    // ensure the closing bracket is consumed via outer helper
                    Err(placeholder)
                }
            })
        })?;

        let (lb_span, rb_span) = spans.expect("array type should provide spans");
        match result {
            Ok((elem_ty, size)) => {
                let (elem_ty, _, ids) = elem_ty.take();
                let mut parsed = Parsed::new(
                    TyScheme::from_mono(Ty::Array(Box::new(elem_ty.into_mono()), size)),
                    self.mk_src(lb_span.extend_to(&rb_span)),
                );
                parsed.set_synthetic_ids(ids);
                Ok(parsed)
            }
            Err(placeholder) => Ok(placeholder),
        }
    }

    fn parse_arr_ty_size(&mut self, ctx: &ParseContext) -> ParseResult<usize> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parsing array type size");
        let ctx = &parser.ctx_clone();
        let size_tok = parser.token()?;
        match &size_tok.kind {
            TokenKind::Integer { suffix, .. } => {
                if suffix.is_some() {
                    return Err(parser.parse_error(
                        "cannot have suffix on static array size".to_string(),
                        size_tok.span,
                        ctx,
                    ));
                }
            }
            _ => {
                return Err(parser.unexpected_token(&size_tok, "static array size", ctx));
            }
        }

        size_tok.to_string().parse::<usize>().map_err(|e| {
            parser.parse_error(
                format!("`{}` is an invalid size: {}", size_tok, e),
                size_tok.span,
                ctx,
            )
        })
    }

    fn parse_generic_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let (name, span) = self.expect_ty_var_ident(ctx)?;
        let id = self.mk_synthetic(span);
        let mut ty = Parsed::new(TyScheme::from_mono(Ty::var(name)), self.mk_src(span));
        ty.set_synthetic_ids(vec![id]);
        Ok(ty)
    }

    pub(crate) fn parse_ty_with_name(
        &mut self,
        name: String,
        span: Span,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        self.parse_ty_with_path(Path::from(name), span, ctx)
    }

    fn parse_ty_with_path(
        &mut self,
        path: Path,
        span: Span,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        let mut synth_ids = vec![];

        let Span { start, mut end } = span;
        let ty_params = self.parse_ty_params(ctx)?;
        if let Some(ref p) = ty_params {
            end = p.rb_span.end;
        }

        let builtin_name = if path.len() == 1 {
            Some(path.as_str())
        } else {
            None
        };
        let ty = if let Some(mut ty) = builtin_name.and_then(Ty::from_str) {
            match &mut ty {
                Ty::Proj(_, el_tys) => {
                    if let Some(ty_params) = ty_params {
                        let (tys, ids): (Vec<_>, Vec<_>) = ty_params
                            .tys
                            .into_iter()
                            .map(|p| {
                                let (ty, _, ids) = p.take();
                                (ty, ids)
                            })
                            .unzip();

                        synth_ids.extend(ids.into_iter().flatten());
                        *el_tys = tys;
                    }
                }
                Ty::RawPtr(ty) => {
                    let count = if let Some(mut ty_params) = ty_params {
                        if ty_params.tys.len() == 0 {
                            0
                        } else {
                            let count = ty_params.tys.len();
                            let parsed_ty = ty_params.tys.remove(0);
                            let (ty_param, _, ids) = parsed_ty.take();
                            synth_ids.extend(ids);
                            *(ty.as_mut()) = ty_param;
                            count
                        }
                    } else {
                        0
                    };

                    if count != 1 {
                        let err = self.parse_error(
                            format!("rawptr expected one type parameter, but found {}", count),
                            span,
                            ctx,
                        );
                        self.record_parse_error(err);
                    }
                }
                _ => {}
            }
            ty
        } else {
            let tys = if let Some(ty_params) = ty_params {
                let (tys, ids): (Vec<_>, Vec<_>) = ty_params
                    .tys
                    .into_iter()
                    .map(|p| {
                        let (ty, _, ids) = p.take();
                        (ty, ids)
                    })
                    .unzip();
                synth_ids.extend(ids.into_iter().flatten());
                tys
            } else {
                vec![]
            };

            Ty::with_tys(path, tys)
        };

        if !matches!(ty, Ty::RawPtr(_)) {
            let base_synth_id = self.mk_synthetic(span);
            synth_ids.insert(0, base_synth_id);
        }

        let mut parsed_ty = Parsed::new(TyScheme::from_mono(ty), self.mk_src(Span { start, end }));
        parsed_ty.set_synthetic_ids(synth_ids);
        Ok(parsed_ty)
    }

    fn parse_fn_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let parser = &mut self.with_scope(ctx).with_description("parse function type");
        let ctx = &parser.ctx_clone();
        // fn[<ty_params>](<params>) -> <ret_ty>
        let fn_span = parser.expect_keyword(TokenKind::Fn, ctx)?;
        let start = fn_span.start;
        let ty_params = parser.parse_ty_params(ctx)?;
        let (params_ty, params_src, param_ids) =
            parser.parse_tuple_ty(ctx)?.map(|t| t.into_mono()).take();
        let mut end = params_src.span.unwrap().end;
        let mut synth_ids = param_ids;
        let ret_ty = Box::new(if peek!(parser, TokenKind::Arrow) {
            parser.expect_end(TokenKind::Arrow, ctx)?;
            let ty = parser.parse_type_annotation(None, ctx);
            let (ty, src, ret_ids) = ty.take();
            end = src.span.unwrap().end;
            synth_ids.extend(ret_ids);
            ty.into_mono()
        } else {
            Ty::unit()
        });

        let param_tys = match params_ty {
            Ty::Tuple(tys) => tys,
            ty => vec![ty],
        };
        let fn_ty = Ty::Func(param_tys, ret_ty);

        let mut parsed = Parsed::new(
            if let Some(ty_params) = ty_params {
                TyScheme::new(
                    ty_params
                        .tys
                        .into_iter()
                        .map(|t| variant!(t.take_value(), if Ty::Var(v)))
                        .collect(),
                    vec![], // TODO: what about predicates?
                    fn_ty,
                )
            } else {
                TyScheme::from_mono(fn_ty)
            },
            parser.mk_src(Span { start, end }),
        );
        parsed.set_synthetic_ids(synth_ids);
        Ok(parsed)
    }

    fn parse_tuple_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let ((tys, trailing), spans) =
            self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                parser.parse_sep_seq(
                    &TokenKind::Comma,
                    trailing,
                    stop.as_ref(),
                    ctx,
                    |parser, ctx| Ok(parser.parse_type_annotation(stop.as_ref(), ctx)),
                )
            })?;

        let (l_span, r_span) = spans.expect("tuple type should provide spans");
        if tys.len() == 1 && !trailing {
            Ok(tys.into_iter().next().unwrap())
        } else {
            let (tys, ids): (Vec<_>, Vec<_>) = tys
                .into_iter()
                .map(|t| {
                    let (ty, _, ids) = t.take();
                    (ty.into_mono(), ids)
                })
                .unzip();
            let mut parsed = Parsed::new(
                TyScheme::from_mono(Ty::Tuple(tys)),
                self.mk_src(l_span.extend_to(&r_span)),
            );
            parsed.set_synthetic_ids(ids.into_iter().flatten().collect());
            Ok(parsed)
        }
    }
}

#[cfg(test)]
mod tests {
    use ray_shared::file_id::FileId;
    use ray_shared::node_id::NodeId;
    use ray_shared::pathlib::{FilePath, Path};
    use ray_shared::span::parsed::Parsed;
    use ray_typing::types::TyScheme;

    use crate::{
        errors::RayError,
        parse::{ParseContext, ParseOptions, Parser},
        sourcemap::SourceMap,
    };

    fn test_options() -> ParseOptions {
        let mut options = ParseOptions::default();
        let filepath = FilePath::from("test.ray");
        options.filepath = filepath.clone();
        options.original_filepath = filepath;
        options.module_path = Path::from("test");
        options
    }

    fn parse<F>(src: &str, mut f: F) -> (Result<Parsed<TyScheme>, RayError>, SourceMap)
    where
        F: FnMut(&mut Parser<'_>) -> Result<Parsed<TyScheme>, RayError>,
    {
        let options = test_options();
        let mut srcmap = SourceMap::new();
        let mut parser = Parser::new(FileId(0), src, options, &mut srcmap);
        let result = f(&mut parser);
        (result, srcmap)
    }

    fn parse_ty(src: &str) -> (Parsed<TyScheme>, SourceMap) {
        let (result, srcmap) = parse(src, |p| {
            let ctx = ParseContext::new(Path::from("test"));
            p.parse_ty(&ctx)
        });
        let ty = result.expect("failed to parse");
        (ty, srcmap)
    }

    fn span_of(id: NodeId, srcmap: &SourceMap) -> (usize, usize) {
        let span = srcmap
            .get_by_id(id)
            .and_then(|s| s.span)
            .expect("could not find span");
        (span.start.offset, span.end.offset)
    }

    #[test]
    fn parses_and_collects_base_ty_synthetic_ids() {
        let (t, srcmap) = parse_ty("A");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 1);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);
    }

    #[test]
    fn parses_and_collects_ty_with_vars_synthetic_ids() {
        let (t, srcmap) = parse_ty("A['a, 'b]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 3);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);

        // 'a
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 2);
        assert_eq!(end, 4);

        // 'b
        let (start, end) = span_of(ids[2], &srcmap);
        assert_eq!(start, 6);
        assert_eq!(end, 8);
    }

    #[test]
    fn parses_and_collects_proj_ty_synthetic_ids() {
        let (t, srcmap) = parse_ty("A[B]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 2);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 2);
        assert_eq!(end, 3);
    }

    #[test]
    fn parses_and_collects_rawptr_ty_synthetic_ids() {
        // rawptr is ignored
        let (t, srcmap) = parse_ty("(rawptr[A], rawptr[B])");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 2);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 8);
        assert_eq!(end, 9);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 19);
        assert_eq!(end, 20);
    }

    #[test]
    fn parses_and_collects_array_ty_synthetic_ids() {
        let (t, srcmap) = parse_ty("[A; 1]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 1);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 1);
        assert_eq!(end, 2);
    }

    #[test]
    fn parses_and_collects_tuple_ty_synthetic_ids() {
        let (t, srcmap) = parse_ty("(A, (B, C), ((D, E), F))");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 6);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 1);
        assert_eq!(end, 2);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 5);
        assert_eq!(end, 6);

        // C
        let (start, end) = span_of(ids[2], &srcmap);
        assert_eq!(start, 8);
        assert_eq!(end, 9);

        // D
        let (start, end) = span_of(ids[3], &srcmap);
        assert_eq!(start, 14);
        assert_eq!(end, 15);

        // E
        let (start, end) = span_of(ids[4], &srcmap);
        assert_eq!(start, 17);
        assert_eq!(end, 18);

        // F
        let (start, end) = span_of(ids[5], &srcmap);
        assert_eq!(start, 21);
        assert_eq!(end, 22);
    }

    #[test]
    fn parses_and_collects_proj_ty_multi_param_synthetic_ids() {
        let (t, srcmap) = parse_ty("A[B, C]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 3);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 2);
        assert_eq!(end, 3);

        // C
        let (start, end) = span_of(ids[2], &srcmap);
        assert_eq!(start, 5);
        assert_eq!(end, 6);
    }

    #[test]
    fn parses_and_collects_nested_ty_synthetic_ids() {
        let (t, srcmap) = parse_ty("A[B, C[T, U]]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 5);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 2);
        assert_eq!(end, 3);

        // C
        let (start, end) = span_of(ids[2], &srcmap);
        assert_eq!(start, 5);
        assert_eq!(end, 6);

        // T
        let (start, end) = span_of(ids[3], &srcmap);
        assert_eq!(start, 7);
        assert_eq!(end, 8);

        // U
        let (start, end) = span_of(ids[4], &srcmap);
        assert_eq!(start, 10);
        assert_eq!(end, 11);
    }

    #[test]
    fn parses_and_collects_nested_ty_with_tuples_synthetic_ids() {
        let (t, srcmap) = parse_ty("A[B, (C[(T, U), V], D[W])]");
        let ids = t.synthetic_ids();
        assert_eq!(ids.len(), 8);

        // A
        let (start, end) = span_of(ids[0], &srcmap);
        assert_eq!(start, 0);
        assert_eq!(end, 1);

        // B
        let (start, end) = span_of(ids[1], &srcmap);
        assert_eq!(start, 2);
        assert_eq!(end, 3);

        // C
        let (start, end) = span_of(ids[2], &srcmap);
        assert_eq!(start, 6);
        assert_eq!(end, 7);

        // T
        let (start, end) = span_of(ids[3], &srcmap);
        assert_eq!(start, 9);
        assert_eq!(end, 10);

        // U
        let (start, end) = span_of(ids[4], &srcmap);
        assert_eq!(start, 12);
        assert_eq!(end, 13);

        // V
        let (start, end) = span_of(ids[5], &srcmap);
        assert_eq!(start, 16);
        assert_eq!(end, 17);

        // D
        let (start, end) = span_of(ids[6], &srcmap);
        assert_eq!(start, 20);
        assert_eq!(end, 21);

        // W
        let (start, end) = span_of(ids[7], &srcmap);
        assert_eq!(start, 22);
        assert_eq!(end, 23);
    }
}
