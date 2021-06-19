use crate::{
    ast::{token::TokenKind, FnParam, Name, Node, TypeParams},
    parse::{ParseResult, Parser},
    span::{parsed::Parsed, Span},
    typing::ty::Ty,
};

impl Parser<'_> {
    pub(crate) fn parse_trait_fn_param(&mut self) -> ParseResult<Node<FnParam>> {
        let (name, span) = self.expect_id()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_ty()?;
        Ok(self.mk_node(FnParam::Name(Name::typed(name, ty)), span))
    }

    pub(crate) fn parse_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        self.parse_ty_with(None)
    }

    fn parse_ty_with(&mut self, ty: Option<Parsed<Ty>>) -> ParseResult<Parsed<Ty>> {
        let ty = if let Some(ty) = ty {
            ty
        } else {
            self.parse_ty_base(None)?
        };

        let ty = self.parse_nilable_ty(ty)?;
        self.parse_union_ty(ty)
    }

    fn parse_nilable_ty(&mut self, ty: Parsed<Ty>) -> ParseResult<Parsed<Ty>> {
        Ok(if peek!(self, TokenKind::Question) {
            let start = ty.span().unwrap().start;
            let end = self.expect_end(TokenKind::Question)?;
            Parsed::new(
                Ty::nilable(ty.take_value()),
                self.mk_src(Span { start, end }),
            )
        } else {
            ty
        })
    }

    fn parse_union_ty(&mut self, ty: Parsed<Ty>) -> ParseResult<Parsed<Ty>> {
        if !expect_if!(self, TokenKind::Pipe) {
            return Ok(ty);
        }

        let next_ty = self.parse_ty()?;
        let span = *ty.span().unwrap();
        let next_span = *next_ty.span().unwrap();
        Ok(match (ty.take_value(), next_ty.take_value()) {
            (Ty::Union(lhs), Ty::Union(rhs)) => {
                let mut tys = lhs;
                tys.extend(rhs);
                Parsed::new(Ty::Union(tys), self.mk_src(span.extend_to(&next_span)))
            }
            (Ty::Union(lhs), ty) => {
                let mut tys = lhs;
                tys.push(ty);
                Parsed::new(Ty::Union(tys), self.mk_src(span.extend_to(&next_span)))
            }
            (ty, Ty::Union(tys)) => {
                Parsed::new(ty, self.mk_src(span));
                Parsed::new(Ty::Union(tys), self.mk_src(span.extend_to(&next_span)))
            }
            (lhs_ty, rhs_ty) => Parsed::new(
                Ty::Union(vec![lhs_ty, rhs_ty]),
                self.mk_src(span.extend_to(&next_span)),
            ),
        })
    }

    pub(crate) fn parse_ty_params(&mut self) -> ParseResult<Option<TypeParams>> {
        if !peek!(self, TokenKind::LeftBracket) {
            Ok(None)
        } else {
            let mut tys = Vec::new();
            let lb_span = self.expect_sp(TokenKind::LeftBracket)?;
            loop {
                tys.push(self.parse_ty()?);
                if peek!(self, TokenKind::RightBracket) {
                    break;
                }

                self.expect(TokenKind::Comma)?;
            }

            let rb_span = self.expect_sp(TokenKind::RightBracket)?;
            Ok(Some(TypeParams {
                tys,
                lb_span,
                rb_span,
            }))
        }
    }

    fn parse_ty_complex(&mut self) -> ParseResult<Option<Parsed<Ty>>> {
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

    fn parse_ty_base(&mut self, ident: Option<(String, Span)>) -> ParseResult<Parsed<Ty>> {
        if let Some(t) = self.parse_ty_complex()? {
            Ok(t)
        } else if let Some((name, span)) = ident {
            self.parse_ty_with_name(name, span)
        } else {
            let (name, span) = self.expect_id()?;
            self.parse_ty_with_name(name, span)
        }
    }

    fn parse_ptr_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        let start = self.expect_start(TokenKind::Asterisk)?;
        let ptee_ty = self.parse_ty()?;
        let end = ptee_ty.span().unwrap().end;
        Ok(Parsed::new(
            Ty::ptr(ptee_ty.take_value()),
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_arr_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        let start = self.expect_start(TokenKind::LeftBracket)?;
        let el_ty = self.parse_ty()?;
        self.expect(TokenKind::Semi)?;

        let size_tok = self.token()?;
        match &size_tok.kind {
            TokenKind::Integer { suffix, .. } => {
                if suffix.is_some() {
                    return Err(self.parse_error(
                        format!("cannot have suffix on static array size"),
                        size_tok.span,
                    ));
                }
            }
            _ => return Err(self.unexpected_token(&size_tok, "static array size")),
        }

        let size = size_tok.to_string().parse::<usize>().map_err(|e| {
            self.parse_error(
                format!("`{}` is an invalid size: {}", size_tok, e),
                size_tok.span,
            )
        })?;

        let rbrack_sp = self.expect_sp(TokenKind::RightBracket)?;
        let end = rbrack_sp.end;

        Ok(Parsed::new(
            Ty::Array(Box::new(el_ty.take_value()), size),
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_generic_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        let (name, span) = self.expect_ty_var_ident()?;
        Ok(Parsed::new(Ty::var(name), self.mk_src(span)))
    }

    pub(crate) fn parse_ty_with_name(
        &mut self,
        name: String,
        span: Span,
    ) -> ParseResult<Parsed<Ty>> {
        let Span { start, mut end } = span;
        let ty_params = self.parse_ty_params()?;
        if let Some(ref p) = ty_params {
            end = p.rb_span.end;
        }

        let ty = if let Some(mut ty) = Ty::from_str(&name) {
            match &mut ty {
                Ty::Projection(name, el_tys) if name.as_str() == "list" => {
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
            Ty::Projection(
                name,
                ty_params
                    .map(|p| p.tys.into_iter().map(|t| t.take_value()).collect())
                    .unwrap_or_default(),
            )
        };

        Ok(Parsed::new(ty, self.mk_src(Span { start, end })))
    }

    fn parse_fn_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        let start = self.expect_start(TokenKind::UpperFn)?;
        let ty_params = self.parse_ty_params()?;
        let params = self.parse_tuple_ty()?;
        let mut end = params.span().unwrap().end;
        let ret_ty = Box::new(if peek!(self, TokenKind::Arrow) {
            self.expect_end(TokenKind::Arrow)?;
            let ty = self.parse_ty()?;
            end = ty.span().unwrap().end;
            ty.take_value()
        } else {
            Ty::unit()
        });

        let param_tys = variant!(params.take_value(), if Ty::Tuple(tys));
        let fn_ty = Ty::Func(param_tys, ret_ty);

        Ok(Parsed::new(
            if let Some(ty_params) = ty_params {
                Ty::All(
                    ty_params
                        .tys
                        .into_iter()
                        .map(|t| variant!(t.take_value(), if Ty::Var(v)))
                        .collect(),
                    Box::new(fn_ty),
                )
            } else {
                fn_ty
            },
            self.mk_src(Span { start, end }),
        ))
    }

    fn parse_tuple_ty(&mut self) -> ParseResult<Parsed<Ty>> {
        let (lparen_tok, lp_span) = self.expect(TokenKind::LeftParen)?;
        let start = lp_span.start;

        let mut tys = Vec::new();
        let mut trailing = false;
        while !peek!(self, TokenKind::RightParen) {
            tys.push(self.parse_ty()?);

            if !peek!(self, TokenKind::RightParen) {
                self.expect(TokenKind::Comma)?;
                trailing = true;
            }
        }

        let end = self.expect_matching(&lparen_tok, TokenKind::RightParen)?;

        Ok(if tys.len() == 1 && !trailing {
            // single element tuple type is just the first type
            // unless there was a trailing ',' after the type e.g.: (T,)
            tys.pop().unwrap()
        } else {
            Parsed::new(
                Ty::Tuple(tys.into_iter().map(|t| t.take_value()).collect()),
                self.mk_src(Span { start, end }),
            )
        })
    }
}
