use std::convert::TryFrom;

use super::{DocComments, ExprResult, ParseContext, ParseResult, Parser, Recover, Restrictions};

use crate::{
    ast::{
        Block, Closure, Expr, Literal, Missing, Name, Node, Path, Pattern, Sequence, Trailing,
        Tuple, ValueKind, token::TokenKind,
    },
    span::{Pos, Span},
};

impl Parser<'_> {
    pub(crate) fn parse_atom(&mut self, ctx: &ParseContext) -> ExprResult {
        ctx.with_description("parsing an atomic expression", |ctx| {
            let tok = self.peek()?;
            match tok.kind {
                TokenKind::Integer { .. }
                | TokenKind::Float { .. }
                | TokenKind::Bool(..)
                | TokenKind::Nil => {
                    let tok = self.token()?;
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
                    let pos = self.lex.position();
                    log::debug!("expected expression but found {} at pos {}", tok, pos);
                    Err(self.unexpected_token(&tok, expected, ctx))
                }
            }
        })
    }

    pub(crate) fn parse_path(&mut self, ctx: &ParseContext) -> ParseResult<Node<Path>> {
        let (id, span) = self.expect_id(ctx)?;
        if expect_if!(self, TokenKind::DoubleColon) {
            self.parse_path_with((id, span), ctx)
        } else {
            Ok(self.mk_node(Path::from(vec![id]), span))
        }
    }

    pub(crate) fn parse_path_with(
        &mut self,
        first: (String, Span),
        ctx: &ParseContext,
    ) -> ParseResult<Node<Path>> {
        // This assumes that the double colon after `first` has been consumed
        let (id, mut span) = first;
        let mut parts = vec![id];
        loop {
            let (id, sp) = self.expect_id(ctx)?;
            parts.push(id);

            span.end = sp.end;
            if !expect_if!(self, TokenKind::DoubleColon) {
                break;
            }
        }

        Ok(self.mk_node(Path::from(parts), span))
    }

    pub(crate) fn parse_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Node<Pattern>> {
        ctx.with_description("parse pattern", |ctx| {
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
                        ctx,
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
        })
    }

    pub(crate) fn parse_name(&mut self, ctx: &ParseContext) -> ParseResult<Node<Name>> {
        let (name, span) = self.expect_id(ctx)?;
        Ok(self.mk_node(Name::new(name), span))
    }

    pub(crate) fn parse_name_with_type(
        &mut self,
        stop: Option<&TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Node<Name>> {
        let (name, span) = self.expect_id(ctx)?;
        let mut name = Name::new(name);
        name.ty = if expect_if!(self, TokenKind::Colon) {
            Some(self.parse_type_annotation(stop, ctx))
        } else {
            None
        };

        Ok(self.mk_node(name, span))
    }

    pub(crate) fn parse_paren_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Node<Pattern>> {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        ctx.description = Some("parse paren pattern".to_string());

        // '('
        let start_tok = self.expect(TokenKind::LeftParen, &ctx)?;
        let start = start_tok.span.start;
        let mut seq = self.parse_expr_seq(
            ctx.get_vkind(),
            Trailing::Allow,
            Some(TokenKind::RightParen),
            &ctx,
        )?;

        // ')'
        let end = self.expect_matching(&start_tok, TokenKind::RightParen, &ctx)?;
        let span = Span { start, end };
        let pattern = if seq.items.len() == 1 && !seq.trailing {
            let item = seq.items.pop().unwrap();
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
        ctx.with_description("parse paren expression", |ctx| {
            // '('
            let start_tok = self.expect(TokenKind::LeftParen, ctx)?;
            let start = start_tok.span.start;
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
            let end = self.expect_matching(&start_tok, TokenKind::RightParen, &ctx)?;

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
                return self.parse_closure_expr_with_seq(
                    args,
                    false,
                    None,
                    Span { start, end },
                    &ctx,
                );
            }

            Ok(self.mk_expr(kind, Span { start, end }, ctx.path.clone()))
        })
    }

    pub(crate) fn parse_name_seq(
        &mut self,
        trail: Trailing,
        stop: Option<&TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Node<Name>>, Span)> {
        ctx.with_description("parse name sequence", |ctx| {
            let mut names = vec![];
            let mut start = Pos::empty();
            let mut end = Pos::empty();
            loop {
                let maybe_name =
                    self.parse_name_with_type(stop, ctx)
                        .map(Some)
                        .recover_seq(self, None, |_| None);

                match maybe_name {
                    Some(n) => {
                        let span = self.srcmap.span_of(&n);
                        if start.is_empty() {
                            start = span.start;
                        }
                        end = span.end;
                        names.push(n);
                    }
                    None => {
                        if peek!(self, TokenKind::Comma) {
                            let span = self.expect_sp(TokenKind::Comma, ctx)?;
                            if matches!(trail, Trailing::Disallow) {
                                Err(self.parse_error(
                                    "unexpected trailing comma".to_string(),
                                    span,
                                    ctx,
                                ))
                                .recover_seq(self, None, |_| ());
                                break;
                            }
                            continue;
                        }
                        if !peek!(self, TokenKind::Identifier(_)) {
                            break;
                        }
                        continue;
                    }
                }

                if !peek!(self, TokenKind::Identifier(_)) {
                    if peek!(self, TokenKind::Comma) {
                        let span = self.expect_sp(TokenKind::Comma, ctx)?;
                        match trail {
                            Trailing::Disallow => {
                                Err(self.parse_error(
                                    "unexpected trailing comma".to_string(),
                                    span,
                                    ctx,
                                ))
                                .recover_seq(self, None, |_| ());
                            }
                            _ => {}
                        }
                    }
                    break;
                }
            }

            Ok((names, Span { start, end }))
        })
    }

    pub(crate) fn parse_expr_seq(
        &mut self,
        vkind: ValueKind,
        trail: Trailing,
        stop_token: Option<TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Sequence> {
        ctx.with_description("parse expression sequence", |ctx| {
            let mut items = vec![];
            let mut trailing = false;
            loop {
                let next_kind = match self.must_peek_kind().map(Some).recover_seq(
                    self,
                    stop_token.as_ref(),
                    |_| None,
                ) {
                    Some(k) => k,
                    None => break,
                };
                match (vkind, next_kind, &stop_token) {
                    (_, k, Some(t)) if &k == t => break,
                    (ValueKind::LValue, TokenKind::Identifier(_), _) => {
                        let maybe_name = self
                            .parse_name_with_type(stop_token.as_ref(), ctx)
                            .map(Some)
                            .recover_seq(self, stop_token.as_ref(), |_| None);
                        match maybe_name {
                            Some(n) => {
                                let span = self.srcmap.span_of(&n);
                                items.push(self.mk_expr(
                                    Expr::Name(n.value),
                                    span,
                                    ctx.path.clone(),
                                ))
                            }
                            None => {
                                if expect_if!(self, TokenKind::Comma) {
                                    trailing = matches!(trail, Trailing::Allow | Trailing::Warn);
                                    continue;
                                }
                                if let Some(stop) = stop_token.as_ref() {
                                    if self.peek_kind().similar_to(stop) {
                                        break;
                                    }
                                }
                                if self.is_eof() {
                                    break;
                                }
                                continue;
                            }
                        }
                    }
                    (ValueKind::RValue, _, _) => {
                        let maybe_expr = self.parse_expr(ctx).map(Some).recover_seq(
                            self,
                            stop_token.as_ref(),
                            |_| None,
                        );
                        match maybe_expr {
                            Some(ex) => {
                                if let Expr::Sequence(seq) = ex.value {
                                    items.extend(seq.items);
                                } else {
                                    items.push(ex);
                                }
                            }
                            None => {
                                if expect_if!(self, TokenKind::Comma) {
                                    trailing = matches!(trail, Trailing::Allow | Trailing::Warn);
                                    continue;
                                }
                                if let Some(stop) = stop_token.as_ref() {
                                    if self.peek_kind().similar_to(stop) {
                                        break;
                                    }
                                }
                                if self.is_eof() {
                                    break;
                                }
                                continue;
                            }
                        }
                    }
                    (_, TokenKind::Comma, _)
                        if matches!(trail, Trailing::Allow | Trailing::Warn) =>
                    {
                        trailing = true;
                    }
                    _ => break,
                }

                if !peek!(self, TokenKind::Comma) {
                    break;
                }

                self.expect(TokenKind::Comma, ctx)?;
            }
            Ok(Sequence { items, trailing })
        })
    }

    pub(crate) fn parse_closure_expr_with_seq(
        &mut self,
        args: Sequence,
        has_curly: bool,
        mut curly_spans: Option<(Span, Span)>,
        mut span: Span,
        ctx: &ParseContext,
    ) -> ExprResult {
        ctx.with_description("parsing closure expression with sequence", |ctx| {
            let arrow_span = Some(self.expect_sp(TokenKind::FatArrow, ctx)?);

            let body = self.parse_expr(ctx)?;

            if has_curly {
                let r = self.expect_sp(TokenKind::RightCurly, ctx)?;
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
        })
    }

    pub(crate) fn parse_closure_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        ctx.with_description("parse closure expression", |ctx| {
            let mut span = Span::new();
            let has_curly = peek!(self, TokenKind::LeftCurly);
            let mut curly_spans = None;
            if has_curly {
                let l = self.expect_sp(TokenKind::LeftCurly, ctx)?;
                span.start = l.start;

                // handle an empty closure
                if peek!(self, TokenKind::RightCurly) {
                    let r = self.expect_sp(TokenKind::RightCurly, ctx)?;
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
                let mut ctx = ctx.clone();
                ctx.restrictions |= Restrictions::IN_PAREN;
                ctx.description = Some("parse closure expression args".to_string());

                let start_tok = self.expect(TokenKind::LeftParen, &ctx)?;
                if !has_curly {
                    span.start = start_tok.span.start;
                }

                let seq = self.parse_expr_seq(
                    ctx.get_vkind(),
                    Trailing::Allow,
                    Some(TokenKind::RightParen),
                    &ctx,
                )?;

                span.end = self.expect_matching(&start_tok, TokenKind::RightParen, &ctx)?;
                seq
            } else {
                // single arg or underscore
                let name = self.parse_name_with_type(None, ctx)?;
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
        })
    }

    pub(crate) fn parse_block(&mut self, ctx: &ParseContext) -> ExprResult {
        ctx.with_description("parse block", |ctx| {
            // '{'
            let start = self.expect(TokenKind::LeftCurly, &ctx)?.span.start;
            let mut stmts = vec![];
            while !peek!(self, TokenKind::RightCurly) {
                let DocComments {
                    module: _,
                    item: doc,
                } = self.parse_doc_comments();
                let stmt = self.parse_stmt(None, doc, ctx).recover_with(
                    self,
                    Some(&TokenKind::RightCurly),
                    |parser, _| {
                        let info = Missing::new("statement", Some(ctx.path.to_string()));
                        parser.mk_expr(Expr::Missing(info), Span::new(), ctx.path.clone())
                    },
                );
                if matches!(stmt.value, Expr::Missing(_))
                    && (peek!(self, TokenKind::RightCurly) || self.is_eof())
                {
                    break;
                }
                stmts.push(stmt);

                if peek!(self, TokenKind::RightCurly) {
                    break;
                }
                self.expect_semi_or_eol(ctx)?;
            }

            // '}'
            let end = self.expect_end(TokenKind::RightCurly, ctx).recover_with(
                self,
                Some(&TokenKind::RightCurly),
                |parser, recovered_end| {
                    if peek!(parser, TokenKind::RightCurly) {
                        parser
                            .expect_end(TokenKind::RightCurly, ctx)
                            .unwrap_or(recovered_end)
                    } else {
                        recovered_end
                    }
                },
            );

            Ok(self.mk_expr(
                Expr::Block(Block::new(stmts)),
                Span { start, end },
                ctx.path.clone(),
            ))
        })
    }
}
