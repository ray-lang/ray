use super::Recover;
use top::Predicates;

use crate::{
    ast::{FnParam, Name, Node, TypeParams, token::TokenKind},
    parse::{ParseResult, Parser},
    span::{Span, parsed::Parsed},
    typing::ty::{Ty, TyScheme},
};

impl Parser<'_> {
    pub(crate) fn parse_trait_fn_param(&mut self) -> ParseResult<Node<FnParam>> {
        let (name, span) = self.expect_id()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type_annotation(Some(&TokenKind::Comma));
        Ok(self.mk_node(FnParam::Name(Name::typed(name, ty)), span))
    }

    pub(crate) fn parse_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        self.parse_ty_with(None)
    }

    fn parse_ty_with(&mut self, ty: Option<Parsed<TyScheme>>) -> ParseResult<Parsed<TyScheme>> {
        let ty = if let Some(ty) = ty {
            ty
        } else {
            self.parse_ty_base(None)?
        };

        let ty = self.parse_nilable_ty(ty)?;
        self.parse_union_ty(ty)
    }

    fn parse_nilable_ty(&mut self, ty: Parsed<TyScheme>) -> ParseResult<Parsed<TyScheme>> {
        Ok(if peek!(self, TokenKind::Question) {
            let start = ty.span().unwrap().start;
            let end = self.expect_end(TokenKind::Question)?;
            Parsed::new(
                TyScheme::from_mono(Ty::nilable(ty.take_value().into_mono())),
                self.mk_src(Span { start, end }),
            )
        } else {
            ty
        })
    }

    fn parse_union_ty(&mut self, ty: Parsed<TyScheme>) -> ParseResult<Parsed<TyScheme>> {
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
            let next_ty = self.parse_type_annotation(Some(&TokenKind::Pipe));
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

    pub(crate) fn parse_ty_params(&mut self) -> ParseResult<Option<TypeParams>> {
        if !peek!(self, TokenKind::LeftBracket) {
            Ok(None)
        } else {
            let mut tys = Vec::new();
            let lb_span = self.expect_sp(TokenKind::LeftBracket)?;
            loop {
                let ty = self.parse_type_annotation(Some(&TokenKind::RightBracket));
                tys.push(ty.map(|ty| ty.into_mono()));

                if peek!(self, TokenKind::RightBracket) {
                    break;
                }

                let had_comma = self.expect(TokenKind::Comma).map(|_| true).recover_seq(
                    self,
                    Some(&TokenKind::RightBracket),
                    |_| false,
                );

                if !had_comma {
                    if peek!(self, TokenKind::RightBracket) || self.is_eof() {
                        break;
                    }
                    continue;
                }
            }

            let rb_span = self.expect_sp(TokenKind::RightBracket)?;
            Ok(Some(TypeParams {
                tys,
                lb_span,
                rb_span,
            }))
        }
    }

    fn parse_ty_complex(&mut self) -> ParseResult<Option<Parsed<TyScheme>>> {
        Ok(if peek!(self, TokenKind::Asterisk) {
            Some(self.parse_ptr_ty()?)
        } else if peek!(self, TokenKind::UpperFn) {
            Some(self.parse_fn_ty()?)
        } else if peek!(self, TokenKind::LeftBracket) {
            Some(self.parse_arr_ty()?)
        } else if peek!(self, TokenKind::SingleQuote) {
            Some(self.parse_generic_ty()?)
        } else if peek!(self, TokenKind::LeftParen) {
            Some(self.parse_tuple_ty()?)
        } else {
            None
        })
    }

    fn parse_ty_base(&mut self, ident: Option<(String, Span)>) -> ParseResult<Parsed<TyScheme>> {
        if let Some(t) = self.parse_ty_complex()? {
            Ok(t)
        } else if let Some((name, span)) = ident {
            self.parse_ty_with_name(name, span)
        } else {
            let (name, span) = self.expect_id()?;
            self.parse_ty_with_name(name, span)
        }
    }

    fn parse_ptr_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        let start = self.expect_start(TokenKind::Asterisk)?;
        let ptee_ty = self.parse_type_annotation(None);
        let end = ptee_ty.span().unwrap().end;
        Ok(Parsed::new(
            TyScheme::from_mono(Ty::ptr(ptee_ty.take_value().into_mono())),
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_arr_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        let start = self.expect_start(TokenKind::LeftBracket)?;
        let el_ty = self.parse_type_annotation(Some(&TokenKind::Semi));
        let elem_ty = el_ty.clone_value().into_mono();
        self.expect(TokenKind::Semi)?;
        let size = match self.parse_arr_ty_size() {
            Ok(size) => size,
            Err(err) => {
                let placeholder = Err(err).recover_with(
                    self,
                    Some(&TokenKind::RightBracket),
                    |parser, recovered| parser.missing_type(start, recovered),
                );
                let _ = self
                    .expect_sp(TokenKind::RightBracket)
                    .map(|_| ())
                    .recover_with(self, None, |_, _| ());
                return Ok(placeholder);
            }
        };
        let rbrack_sp = self.expect_sp(TokenKind::RightBracket)?;
        let end = rbrack_sp.end;

        Ok(Parsed::new(
            TyScheme::from_mono(Ty::Array(Box::new(elem_ty), size)),
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_arr_ty_size(&mut self) -> ParseResult<usize> {
        let size_tok = self.token()?;
        match &size_tok.kind {
            TokenKind::Integer { suffix, .. } => {
                if suffix.is_some() {
                    return Err(self.parse_error(
                        "cannot have suffix on static array size".to_string(),
                        size_tok.span,
                    ));
                }
            }
            _ => return Err(self.unexpected_token(&size_tok, "static array size")),
        }

        size_tok.to_string().parse::<usize>().map_err(|e| {
            self.parse_error(
                format!("`{}` is an invalid size: {}", size_tok, e),
                size_tok.span,
            )
        })
    }

    fn parse_generic_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        let (name, span) = self.expect_ty_var_ident()?;
        Ok(Parsed::new(
            TyScheme::from_mono(Ty::var(name)),
            self.mk_src(span),
        ))
    }

    pub(crate) fn parse_ty_with_name(
        &mut self,
        name: String,
        span: Span,
    ) -> ParseResult<Parsed<TyScheme>> {
        let Span { start, mut end } = span;
        let ty_params = self.parse_ty_params()?;
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

    fn parse_fn_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        // Fn[<ty_params>](<params>) -> <ret_ty>
        let fn_span = self.expect_keyword(TokenKind::UpperFn)?;
        let start = fn_span.start;
        let ty_params = self.parse_ty_params()?;
        let params = self.parse_tuple_ty()?.map(|t| t.into_mono());
        let mut end = params.span().unwrap().end;
        let ret_ty = Box::new(if peek!(self, TokenKind::Arrow) {
            self.expect_end(TokenKind::Arrow)?;
            let ty = self.parse_type_annotation(None);
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
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_tuple_ty(&mut self) -> ParseResult<Parsed<TyScheme>> {
        let (lparen_tok, lp_span) = self.expect(TokenKind::LeftParen)?;
        let start = lp_span.start;

        let mut tys = Vec::new();
        let mut last_had_comma = false;
        while !peek!(self, TokenKind::RightParen) && !self.is_eof() {
            let ty = self.parse_type_annotation(Some(&TokenKind::RightParen));
            tys.push(ty);
            last_had_comma = false;

            if peek!(self, TokenKind::RightParen) {
                break;
            }

            let had_comma = self.expect(TokenKind::Comma).map(|_| true).recover_seq(
                self,
                Some(&TokenKind::RightParen),
                |_| false,
            );

            last_had_comma = had_comma;

            if !had_comma {
                if peek!(self, TokenKind::RightParen) || self.is_eof() {
                    break;
                }
                continue;
            }
        }

        let end = self.expect_matching(&lparen_tok, TokenKind::RightParen)?;
        let trailing = last_had_comma;

        Ok(if tys.len() == 1 && !trailing {
            // single element tuple type is just the first type
            // unless there was a trailing ',' after the type e.g.: (T,)
            tys.pop().unwrap()
        } else {
            Parsed::new(
                TyScheme::from_mono(Ty::Tuple(
                    tys.into_iter()
                        .map(|t| t.take_value().into_mono())
                        .collect(),
                )),
                self.mk_src(Span { start, end }),
            )
        })
    }
}
