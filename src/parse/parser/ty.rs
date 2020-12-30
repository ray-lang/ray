use crate::ast::token::{IntegerBase, TokenKind};
use crate::ast::{FloatTy, IntTy, Type, TypeKind, TypeParams};
use crate::parse::{ParseResult, Parser};
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_ty(&mut self) -> ParseResult<Type> {
        let mut ty: Option<Type> = None;
        loop {
            let t = if peek!(self, TokenKind::Asterisk) {
                let start = self.expect_start(TokenKind::Asterisk)?;
                let ptee_ty = self.parse_ty()?;
                let end = ptee_ty.span.unwrap().end;
                Type {
                    kind: TypeKind::pointer(ptee_ty),
                    span: Some(Span { start, end }),
                }
            } else if peek!(self, TokenKind::UpperFn) {
                self.parse_fn_ty()?
            } else if peek!(self, TokenKind::LeftBracket) {
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

                Type {
                    kind: TypeKind::Array(Box::new(el_ty), size),
                    span: Some(Span { start, end }),
                }
            } else {
                let mut t = if peek!(self, TokenKind::LeftParen) {
                    self.parse_tuple_ty()
                } else {
                    self.parse_basic_ty()
                }?;

                if peek!(self, TokenKind::Question) {
                    let start = t.span.unwrap().start;
                    let end = self.expect_end(TokenKind::Question)?;
                    t = Type {
                        kind: TypeKind::optional(t),
                        span: Some(Span { start, end }),
                    }
                }
                t
            };

            if let Some(Type {
                kind: TypeKind::Union(tys),
                span,
            }) = ty.as_mut()
            {
                span.as_mut().unwrap().end = t.span.unwrap().end;
                tys.push(t)
            } else if !peek!(self, TokenKind::Pipe) {
                return Ok(t);
            } else {
                let span = t.span;
                ty = Some(Type {
                    kind: TypeKind::Union(vec![t]),
                    span,
                })
            }

            if !peek!(self, TokenKind::Pipe) {
                return Ok(ty.unwrap());
            }

            // we've got a union type, consume the '|'
            self.expect(TokenKind::Pipe)?;
        }
    }

    pub(crate) fn parse_ty_params(&mut self) -> ParseResult<Option<TypeParams>> {
        if !peek!(self, TokenKind::LeftBracket) {
            Ok(None)
        } else {
            let mut tys = Vec::new();
            let lb_span = self.expect_sp(TokenKind::LeftBracket)?;
            loop {
                tys.push(self.parse_generic_ty()?);
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

    pub(crate) fn parse_ty_args(&mut self) -> ParseResult<Option<(Vec<Type>, Span)>> {
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
            let span = lb_span.extend_to(&rb_span);
            Ok(Some((tys, span)))
        }
    }

    fn parse_generic_ty(&mut self) -> ParseResult<Type> {
        let (name, Span { start, mut end }) = self.expect_id()?;
        let bounds = if expect_if!(self, TokenKind::Colon) {
            let b = self.parse_basic_ty()?;
            end = b.span.unwrap().end;
            Some(Box::new(b))
        } else {
            None
        };

        Ok(Type {
            kind: TypeKind::Generic { name, bounds },
            span: Some(Span { start, end }),
        })
    }

    fn parse_basic_ty(&mut self) -> ParseResult<Type> {
        let (name, Span { start, mut end }) = self.expect_id()?;
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
            let bounds = if expect_if!(self, TokenKind::Colon) {
                Some(Box::new(self.parse_basic_ty()?))
            } else {
                None
            };

            if let Some(ref b) = bounds {
                end = b.as_ref().span.unwrap().end;
            }

            TypeKind::Basic {
                name,
                ty_params,
                bounds,
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
