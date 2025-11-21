use super::{Recover, RecoveryCtx};
use top::Predicates;

use crate::{
    ast::{TrailingPolicy, TypeParams, token::TokenKind},
    parse::{
        ParseContext, ParseResult, Parser,
        lexer::NewlineMode,
        parser::{Restrictions, context::SeqSpec},
    },
    span::{Span, parsed::Parsed},
    typing::ty::{Ty, TyScheme},
};

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

        let ty = self.parse_nilable_ty(ty, ctx)?;
        self.parse_union_ty(ty, ctx)
    }

    fn parse_nilable_ty(
        &mut self,
        ty: Parsed<TyScheme>,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        Ok(if peek!(self, TokenKind::Question) {
            let start = ty.span().unwrap().start;
            let end = self.expect_end(TokenKind::Question, ctx)?;
            Parsed::new(
                TyScheme::from_mono(Ty::nilable(ty.take_value().into_mono())),
                self.mk_src(Span { start, end }),
            )
        } else {
            ty
        })
    }

    fn parse_union_ty(
        &mut self,
        ty: Parsed<TyScheme>,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        if !expect_if!(self, TokenKind::Pipe) {
            return Ok(ty);
        }

        let span = ty.span().copied();
        let start = span.map(|s| s.start).unwrap_or_else(|| self.lex.position());
        let mut end = span.map(|s| s.end).unwrap_or(start);
        let mut items = match ty.take_value().into_mono() {
            Ty::Union(tys) => tys,
            other => vec![other],
        };

        loop {
            let next_ty = self.parse_type_annotation(Some(&TokenKind::Pipe), ctx);
            if let Some(span) = next_ty.span() {
                end = span.end;
            }
            match next_ty.take_value().into_mono() {
                Ty::Union(mut tys) => items.append(&mut tys),
                other => items.push(other),
            }

            if !expect_if!(self, TokenKind::Pipe) {
                break;
            }
        }

        Ok(Parsed::new(
            TyScheme::from_mono(Ty::Union(items)),
            self.mk_src(Span { start, end }),
        ))
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
        } else if let Some((name, span)) = ident {
            self.parse_ty_with_name(name, span, ctx)
        } else {
            let (name, span) = self.expect_id(ctx)?;
            self.parse_ty_with_name(name, span, ctx)
        }
    }

    fn parse_ptr_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let start = self.expect_start(TokenKind::Asterisk, ctx)?;
        let ptee_ty = self.parse_type_annotation(None, ctx);
        let end = ptee_ty.span().unwrap().end;
        Ok(Parsed::new(
            TyScheme::from_mono(Ty::refty(ptee_ty.take_value().into_mono())),
            self.mk_src(Span { start, end }),
        ))
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
            let elem_ty = el_ty.clone_value().into_mono();
            parser.expect(TokenKind::Semi, ctx)?;
            Ok(match parser.parse_arr_ty_size(ctx) {
                Ok(size) => Ok((elem_ty, size)),
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
            Ok((elem_ty, size)) => Ok(Parsed::new(
                TyScheme::from_mono(Ty::Array(Box::new(elem_ty), size)),
                self.mk_src(lb_span.extend_to(&rb_span)),
            )),
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
        Ok(Parsed::new(
            TyScheme::from_mono(Ty::var(name)),
            self.mk_src(span),
        ))
    }

    pub(crate) fn parse_ty_with_name(
        &mut self,
        name: String,
        span: Span,
        ctx: &ParseContext,
    ) -> ParseResult<Parsed<TyScheme>> {
        let Span { start, mut end } = span;
        let ty_params = self.parse_ty_params(ctx)?;
        if let Some(ref p) = ty_params {
            end = p.rb_span.end;
        }

        let ty = if let Some(mut ty) = Ty::from_str(&name) {
            match &mut ty {
                Ty::Projection(_, el_tys) => {
                    *el_tys = ty_params
                        .unwrap()
                        .tys
                        .into_iter()
                        .map(|t| t.take_value())
                        .collect();
                }
                Ty::RawPtr(ty) => {
                    let count = if let Some(mut ty_params) = ty_params {
                        if ty_params.tys.len() == 0 {
                            0
                        } else {
                            let count = ty_params.tys.len();
                            let parsed_ty = ty_params.tys.remove(0);
                            *(ty.as_mut()) = parsed_ty.take_value();
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
            Ty::with_tys(
                &name,
                ty_params
                    .map(|p| p.tys.into_iter().map(|t| t.take_value()).collect())
                    .unwrap_or_default(),
            )
        };

        Ok(Parsed::new(
            TyScheme::from_mono(ty),
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_fn_ty(&mut self, ctx: &ParseContext) -> ParseResult<Parsed<TyScheme>> {
        let parser = &mut self.with_scope(ctx).with_description("parse function type");
        let ctx = &parser.ctx_clone();
        // Fn[<ty_params>](<params>) -> <ret_ty>
        let fn_span = parser.expect_keyword(TokenKind::UpperFn, ctx)?;
        let start = fn_span.start;
        let ty_params = parser.parse_ty_params(ctx)?;
        let params = parser.parse_tuple_ty(ctx)?.map(|t| t.into_mono());
        let mut end = params.span().unwrap().end;
        let ret_ty = Box::new(if peek!(parser, TokenKind::Arrow) {
            parser.expect_end(TokenKind::Arrow, ctx)?;
            let ty = parser.parse_type_annotation(None, ctx);
            end = ty.span().unwrap().end;
            ty.take_value().into_mono()
        } else {
            Ty::unit()
        });

        let param_tys = match params.take_value() {
            Ty::Tuple(tys) => tys,
            ty => vec![ty],
        };
        let fn_ty = Ty::Func(param_tys, ret_ty);

        Ok(Parsed::new(
            if let Some(ty_params) = ty_params {
                TyScheme::new(
                    ty_params
                        .tys
                        .into_iter()
                        .map(|t| variant!(t.take_value(), if Ty::Var(v)))
                        .collect(),
                    Predicates::new(), // TODO: what about predicates?
                    fn_ty,
                )
            } else {
                TyScheme::from_mono(fn_ty)
            },
            parser.mk_src(Span { start, end }),
        ))
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
            Ok(Parsed::new(
                TyScheme::from_mono(Ty::Tuple(
                    tys.into_iter()
                        .map(|t| t.take_value().into_mono())
                        .collect(),
                )),
                self.mk_src(l_span.extend_to(&r_span)),
            ))
        }
    }
}
