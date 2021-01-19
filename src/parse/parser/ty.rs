use crate::{
    ast::{token::TokenKind, FnParam, Name, SourceInfo, Type, TypeKind, TypeParams},
    parse::{ParseResult, Parser},
    span::Span,
};

impl Parser {
    pub(crate) fn parse_trait_fn_param(&mut self) -> ParseResult<FnParam<SourceInfo>> {
        if let Some(ty) = self.parse_ty_complex()? {
            return Ok(FnParam::Type(self.parse_ty_with(Some(ty))?));
        }

        let (name, span) = self.expect_id()?;
        if expect_if!(self, TokenKind::Colon) {
            let ty = self.parse_ty()?;
            return Ok(FnParam::Name(Name {
                name,
                span,
                ty: Some(ty),
            }));
        }

        let ty = self.parse_ty_with_name(name, span)?;
        Ok(FnParam::Type(self.parse_ty_with(Some(ty))?))
    }

    pub(crate) fn parse_ty(&mut self) -> ParseResult<Type> {
        self.parse_ty_with(None)
    }

    fn parse_ty_with(&mut self, mut ty: Option<Type>) -> ParseResult<Type> {
        let ty = if let Some(ty) = ty {
            ty
        } else {
            self.parse_ty_base(None)?
        };

        let ty = self.parse_nilable_ty(ty)?;
        self.parse_union_ty(ty)
    }

    fn parse_nilable_ty(&mut self, ty: Type) -> ParseResult<Type> {
        Ok(if peek!(self, TokenKind::Question) {
            let start = ty.span.unwrap().start;
            let end = self.expect_end(TokenKind::Question)?;
            Type {
                kind: TypeKind::optional(ty),
                span: Some(Span { start, end }),
            }
        } else {
            ty
        })
    }

    fn parse_union_ty(&mut self, ty: Type) -> ParseResult<Type> {
        if !expect_if!(self, TokenKind::Pipe) {
            return Ok(ty);
        }

        let span = ty.span.unwrap();
        let next_ty = self.parse_ty()?;
        let next_span = next_ty.span.unwrap();
        Ok(match (ty.kind, next_ty.kind) {
            (TypeKind::Union(lhs), TypeKind::Union(rhs)) => {
                let mut tys = lhs;
                tys.extend(rhs);
                Type {
                    kind: TypeKind::Union(tys),
                    span: Some(span.extend_to(&next_span)),
                }
            }
            (TypeKind::Union(lhs), kind) => {
                let mut tys = lhs;
                tys.push(Type {
                    kind,
                    span: Some(next_span),
                });
                Type {
                    kind: TypeKind::Union(tys),
                    span: Some(span.extend_to(&next_span)),
                }
            }
            (kind, TypeKind::Union(rhs)) => {
                let mut tys = rhs;
                tys.push(Type {
                    kind,
                    span: Some(span),
                });
                Type {
                    kind: TypeKind::Union(tys),
                    span: Some(span.extend_to(&next_span)),
                }
            }
            (lhs_kind, rhs_kind) => Type {
                kind: TypeKind::Union(vec![
                    Type {
                        kind: lhs_kind,
                        span: Some(span),
                    },
                    Type {
                        kind: rhs_kind,
                        span: Some(next_span),
                    },
                ]),
                span: Some(span.extend_to(&next_span)),
            },
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

    fn parse_ty_complex(&mut self) -> ParseResult<Option<Type>> {
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

    fn parse_ty_base(&mut self, ident: Option<(String, Span)>) -> ParseResult<Type> {
        if let Some(t) = self.parse_ty_complex()? {
            Ok(t)
        } else if let Some((name, span)) = ident {
            self.parse_ty_with_name(name, span)
        } else {
            let (name, span) = self.expect_id()?;
            self.parse_ty_with_name(name, span)
        }
    }

    fn parse_ptr_ty(&mut self) -> ParseResult<Type> {
        let start = self.expect_start(TokenKind::Asterisk)?;
        let ptee_ty = self.parse_ty()?;
        let end = ptee_ty.span.unwrap().end;
        Ok(Type {
            kind: TypeKind::pointer(ptee_ty),
            span: Some(Span { start, end }),
        })
    }

    fn parse_arr_ty(&mut self) -> ParseResult<Type> {
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

        Ok(Type {
            kind: TypeKind::Array(Box::new(el_ty), size),
            span: Some(Span { start, end }),
        })
    }

    fn parse_generic_ty(&mut self) -> ParseResult<Type> {
        let (name, span) = self.expect_ty_var_ident()?;
        Ok(Type {
            kind: TypeKind::Generic(name),
            span: Some(span),
        })
    }

    pub(crate) fn parse_ty_with_name(&mut self, name: String, span: Span) -> ParseResult<Type> {
        let Span { start, mut end } = span;
        let ty_params = self.parse_ty_params()?;
        if let Some(ref p) = ty_params {
            end = p.rb_span.end;
        }

        let kind = if let Some(mut kind) = TypeKind::from_str(&name) {
            if let TypeKind::List(el_ty) = &mut kind {
                let el_ty = el_ty.as_mut();
                *el_ty = ty_params.unwrap().tys.pop().unwrap();
            }

            kind
        } else {
            TypeKind::Basic {
                name,
                ty_params,
                bounds: None,
            }
        };

        Ok(Type {
            kind,
            span: Some(Span { start, end }),
        })
    }

    fn parse_fn_ty(&mut self) -> ParseResult<Type> {
        let start = self.expect_start(TokenKind::UpperFn)?;
        let ty_params = self.parse_ty_params()?;
        let params = self.parse_tuple_ty()?;
        let mut end = params.span.unwrap().end;
        let ret = if peek!(self, TokenKind::Arrow) {
            self.expect_end(TokenKind::Arrow)?;
            let ty = self.parse_ty()?;
            end = ty.span.unwrap().end;
            Some(Box::new(ty))
        } else {
            None
        };
        Ok(Type {
            kind: TypeKind::Fn {
                params: Box::new(params),
                ty_params,
                ret,
            },
            span: Some(Span { start, end }),
        })
    }

    fn parse_tuple_ty(&mut self) -> ParseResult<Type> {
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
            Type {
                kind: TypeKind::Sequence(tys),
                span: Some(Span { start, end }),
            }
        })
    }
}
