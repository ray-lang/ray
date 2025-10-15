use std::convert::TryFrom;

use super::{ExprResult, ParseContext, ParseResult, Parser, Restrictions};

use crate::{
    ast::{
        token::TokenKind, Block, Closure, Expr, Literal, Name, Node, Path, Pattern, Sequence,
        Trailing, Tuple, ValueKind,
    },
    span::{Pos, Span},
};

impl Parser<'_> {
    pub(crate) fn parse_atom(&mut self, ctx: &ParseContext) -> ExprResult {
        let tok = self.token()?;
        match tok.kind {
            TokenKind::Integer { .. }
            | TokenKind::Float { .. }
            | TokenKind::Bool(..)
            | TokenKind::Nil => {
                let span = tok.span;
                Ok(self.mk_expr(
                    Expr::Literal(Literal::from_token(tok, &self.options.filepath, &ctx.path)?),
                    span,
                    ctx.path.clone(),
                ))
            }
            _ => {
                let expected = if ctx
                    .restrictions
                    .contains(Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA)
                {
                    "an expression after the previous comma"
                } else {
                    "an expression"
                };
                Err(self.unexpected_token(&tok, expected))
            }
        }
    }

    pub(crate) fn parse_path(&mut self) -> ParseResult<Node<Path>> {
        let (id, span) = self.expect_id()?;
        if expect_if!(self, TokenKind::DoubleColon) {
            self.parse_path_with((id, span))
        } else {
            Ok(self.mk_node(Path::from(vec![id]), span))
        }
    }

    pub(crate) fn parse_path_with(&mut self, first: (String, Span)) -> ParseResult<Node<Path>> {
        // This assumes that the double colon after `first` has been consumed
        let (id, mut span) = first;
        let mut parts = vec![id];
        loop {
            let (id, sp) = self.expect_id()?;
            parts.push(id);

            span.end = sp.end;
            if !expect_if!(self, TokenKind::DoubleColon) {
                break;
            }
        }

        Ok(self.mk_node(Path::from(parts), span))
    }

    pub(crate) fn parse_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Node<Pattern>> {
        Ok(if peek!(self, TokenKind::LeftParen) {
            self.parse_paren_pattern(ctx)?
        } else {
            let start = self.lex.position();
            let seq = self.parse_expr_seq(ValueKind::LValue, Trailing::Warn, None, ctx)?;
            let end = self.lex.position();
            let span = Span { start, end };
            if seq.items.len() == 0 {
                return Err(self.parse_error(
                    "expected one or more items in pattern, but found none".to_string(),
                    span,
                ));
            }
            self.mk_node(
                Pattern::try_from(seq).map_err(|mut e| {
                    let src = self.mk_src(span);
                    e.src.push(src);
                    e
                })?,
                span,
            )
        })
    }

    pub(crate) fn parse_name(&mut self) -> ParseResult<Node<Name>> {
        let (name, span) = self.expect_id()?;
        Ok(self.mk_node(Name::new(name), span))
    }

    pub(crate) fn parse_name_with_type(&mut self) -> ParseResult<Node<Name>> {
        let (name, span) = self.expect_id()?;
        let mut name = Name::new(name);
        name.ty = if expect_if!(self, TokenKind::Colon) {
            Some(self.parse_ty()?)
        } else {
            None
        };

        Ok(self.mk_node(name, span))
    }

    pub(crate) fn parse_paren_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Node<Pattern>> {
        // '('
        let (start_tok, start_sp) = self.expect(TokenKind::LeftParen)?;
        let start = start_sp.start;
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        let mut seq = self.parse_expr_seq(
            ctx.get_vkind(),
            Trailing::Allow,
            Some(TokenKind::RightParen),
            &ctx,
        )?;

        // ')'
        let end = self.expect_matching(&start_tok, TokenKind::RightParen)?;
        let span = Span { start, end };
        let pattern = if seq.items.len() == 1 && !seq.trailing {
            let item = seq.items.pop().unwrap();
            let src = self.mk_src(span);
            match item.value {
                Expr::Name(n) => Pattern::Name(n),
                _ => unreachable!(),
            }
        } else {
            Pattern::tuple(seq).map_err(|mut e| {
                let src = self.mk_src(span);
                e.src.push(src);
                e
            })?
        };

        Ok(self.mk_node(pattern, span))
    }

    pub(crate) fn parse_paren_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        // '('
        let (start_tok, start_sp) = self.expect(TokenKind::LeftParen)?;
        let start = start_sp.start;
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        let kind = if !peek!(self, TokenKind::RightParen) {
            ctx.stop_token = Some(TokenKind::RightParen);
            let ex = self.parse_expr(&ctx)?;
            if let Expr::Sequence(seq) = ex.value {
                Expr::Tuple(Tuple { seq })
            } else {
                Expr::Paren(Box::new(ex))
            }
        } else {
            Expr::Tuple(Tuple {
                seq: Sequence {
                    items: vec![],
                    trailing: false,
                },
            })
        };
        // ')'
        let end = self.expect_matching(&start_tok, TokenKind::RightParen)?;

        if peek!(self, TokenKind::FatArrow) {
            // closure expression!
            let args = match kind {
                Expr::Tuple(tuple) => tuple.seq,
                Expr::Paren(ex) => Sequence {
                    items: vec![*ex],
                    trailing: false,
                },
                _ => unreachable!(),
            };
            return self.parse_closure_expr_with_seq(args, false, None, Span { start, end }, &ctx);
        }

        Ok(self.mk_expr(kind, Span { start, end }, ctx.path.clone()))
    }

    pub(crate) fn parse_name_seq(
        &mut self,
        trail: Trailing,
        _: &ParseContext,
    ) -> ParseResult<(Vec<Node<Name>>, Span)> {
        let mut names = vec![];
        let mut start = Pos::new();
        let mut end: Pos;
        loop {
            let n = self.parse_name_with_type()?;
            let span = self.srcmap.span_of(&n);
            if start.empty() {
                start = span.start;
            }
            end = span.end;
            names.push(n);

            if !peek!(self, TokenKind::Identifier(_)) {
                if peek!(self, TokenKind::Comma) {
                    let span = self.expect_sp(TokenKind::Comma)?;
                    match trail {
                        Trailing::Disallow => {
                            return Err(
                                self.parse_error("unexpected trailing comma".to_string(), span)
                            )
                        }
                        _ => continue,
                    }
                }
                break;
            }
        }

        Ok((names, Span { start, end }))
    }

    pub(crate) fn parse_expr_seq(
        &mut self,
        vkind: ValueKind,
        trail: Trailing,
        stop_token: Option<TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Sequence> {
        let mut items = vec![];
        let mut trailing = false;
        loop {
            match (vkind, self.must_peek_kind()?, &stop_token) {
                (_, k, Some(t)) if &k == t => break,
                (ValueKind::LValue, TokenKind::Identifier(_), _) => {
                    let n = self.parse_name_with_type()?;
                    let span = self.srcmap.span_of(&n);
                    items.push(self.mk_expr(Expr::Name(n.value), span, ctx.path.clone()))
                }
                (ValueKind::RValue, _, _) => {
                    let ex = self.parse_expr(ctx)?;
                    if let Expr::Sequence(seq) = ex.value {
                        items.extend(seq.items);
                    } else {
                        items.push(ex);
                    }
                }
                (_, TokenKind::Comma, _) if matches!(trail, Trailing::Allow | Trailing::Warn) => {
                    trailing = true;
                }
                _ => break,
            }

            if !peek!(self, TokenKind::Comma) {
                break;
            }

            self.expect(TokenKind::Comma)?;
        }
        Ok(Sequence { items, trailing })
    }

    pub(crate) fn parse_closure_expr_with_seq(
        &mut self,
        args: Sequence,
        has_curly: bool,
        mut curly_spans: Option<(Span, Span)>,
        mut span: Span,
        ctx: &ParseContext,
    ) -> ExprResult {
        let arrow_span = Some(self.expect_sp(TokenKind::FatArrow)?);

        let body = self.parse_expr(ctx)?;

        if has_curly {
            let r = self.expect_sp(TokenKind::RightCurly)?;
            span.end = r.end;
            if let Some((l, _)) = curly_spans {
                curly_spans = Some((l, r));
            }
        }

        Ok(self.mk_expr(
            Expr::Closure(Closure {
                args,
                arrow_span,
                curly_spans,
                body: Box::new(body),
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_closure_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut span = Span::new();
        let has_curly = peek!(self, TokenKind::LeftCurly);
        let mut curly_spans = None;
        if has_curly {
            let l = self.expect_sp(TokenKind::LeftCurly)?;
            span.start = l.start;

            // handle an empty closure
            if peek!(self, TokenKind::RightCurly) {
                let r = self.expect_sp(TokenKind::RightCurly)?;
                span.end = r.end;
                curly_spans = Some((l, r));
                let body = Box::new(self.mk_expr(
                    Expr::Tuple(Tuple {
                        seq: Sequence::empty(),
                    }),
                    span,
                    ctx.path.clone(),
                ));
                return Ok(self.mk_expr(
                    Expr::Closure(Closure {
                        args: Sequence::empty(),
                        arrow_span: None,
                        curly_spans,
                        body,
                    }),
                    span,
                    ctx.path.clone(),
                ));
            }

            curly_spans = Some((l, Span::new()));
        }

        let args = if peek!(self, TokenKind::LeftParen) {
            let (start_tok, start_sp) = self.expect(TokenKind::LeftParen)?;
            if !has_curly {
                span.start = start_sp.start;
            }
            let mut ctx = ctx.clone();
            ctx.restrictions |= Restrictions::IN_PAREN;
            let seq = self.parse_expr_seq(
                ctx.get_vkind(),
                Trailing::Allow,
                Some(TokenKind::RightParen),
                &ctx,
            )?;

            span.end = self.expect_matching(&start_tok, TokenKind::RightParen)?;
            seq
        } else {
            // single arg or underscore
            let name = self.parse_name_with_type()?;
            let name_span = self.srcmap.span_of(&name);
            if !has_curly {
                span.start = name_span.start;
            }

            span.end = name_span.end;
            Sequence {
                items: vec![self.mk_expr(Expr::Name(name.value), name_span, ctx.path.clone())],
                trailing: false,
            }
        };

        self.parse_closure_expr_with_seq(args, has_curly, curly_spans, span, ctx)
    }

    pub(crate) fn parse_block(&mut self, ctx: &ParseContext) -> ExprResult {
        // '{'
        let start = self.expect_start(TokenKind::LeftCurly)?;
        let mut stmts = vec![];
        while !peek!(self, TokenKind::RightCurly) {
            let doc = self.parse_doc_comment();
            stmts.push(self.parse_stmt(None, doc, ctx)?)
        }

        // '}'
        let end = self.expect_end(TokenKind::RightCurly)?;

        Ok(self.mk_expr(
            Expr::Block(Block::new(stmts)),
            Span { start, end },
            ctx.path.clone(),
        ))
    }
}
