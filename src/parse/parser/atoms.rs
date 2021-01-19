use super::{ExprResult, ParseContext, ParseResult, Parser, Restrictions};

use crate::{
    ast::{
        token::TokenKind, Block, Closure, Expr, HasExpr, Literal, Name, Path, Pattern, PatternKind,
        Sequence, SourceInfo, Trailing, ValueKind,
    },
    span::{Pos, Span},
};

impl Parser {
    pub(crate) fn parse_atom(&mut self, ctx: &ParseContext) -> ExprResult {
        let tok = self.token()?;
        match tok.kind {
            TokenKind::Integer { .. }
            | TokenKind::Float { .. }
            | TokenKind::Bool(..)
            | TokenKind::Nil => {
                let span = tok.span;
                Ok(self.mk_expr(
                    Expr::Literal(Literal::from_token(tok, &self.options.filepath)?),
                    span,
                ))
            }
            _ => {
                let expected = if ctx
                    .restrictions
                    .contains(Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA)
                {
                    "an expression after the previous comma"
                } else {
                    "an atom"
                };
                Err(self.unexpected_token(&tok, expected))
            }
        }
    }

    pub(crate) fn parse_path(&mut self) -> ParseResult<Path> {
        let (id, span) = self.expect_id()?;
        if expect_if!(self, TokenKind::DoubleColon) {
            self.parse_path_with((id, span))
        } else {
            let mut p = Path::from(vec![id]);
            p.span = span;
            Ok(p)
        }
    }

    pub(crate) fn parse_path_with(&mut self, first: (String, Span)) -> ParseResult<Path> {
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

        let mut p = Path::from(parts);
        p.span = span;
        Ok(p)
    }

    pub(crate) fn parse_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Pattern<SourceInfo>> {
        Ok(if peek!(self, TokenKind::LeftParen) {
            self.parse_paren_pattern(ctx)?
        } else {
            let start = self.lex.position();
            let mut seq = self.parse_expr_seq(ValueKind::LValue, Trailing::Warn, None, ctx)?;
            let end = self.lex.position();
            let span = Span { start, end };
            if seq.items.len() == 0 {
                return Err(self.parse_error(
                    "expected one or more items in pattern, but found none".to_string(),
                    span,
                ));
            }
            let kind = if seq.items.len() == 1 {
                match seq.items.pop().unwrap().value {
                    Expr::Name(n) => PatternKind::Name(n),
                    Expr::Tuple(t) => PatternKind::Tuple(t),
                    _ => unreachable!(),
                }
            } else {
                PatternKind::Sequence(seq)
            };
            Pattern { kind, span }
        })
    }

    pub(crate) fn parse_name(&mut self) -> ParseResult<Name> {
        let (name, span) = self.expect_id()?;
        Ok(Name {
            name,
            span,
            ty: None,
        })
    }

    pub(crate) fn parse_name_with_type(&mut self) -> ParseResult<Name> {
        let (name, span) = self.expect_id()?;
        let ty = if expect_if!(self, TokenKind::Colon) {
            Some(self.parse_ty()?)
        } else {
            None
        };
        Ok(Name { name, span, ty })
    }

    pub(crate) fn parse_paren_pattern(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Pattern<SourceInfo>> {
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
        Ok(if seq.items.len() == 1 && !seq.trailing {
            let item = seq.items.pop().unwrap();
            match item.value {
                Expr::Name(n) => Pattern {
                    kind: PatternKind::Name(n),
                    span: Span { start, end },
                },
                _ => unreachable!(),
            }
        } else {
            Pattern {
                kind: PatternKind::Tuple(seq),
                span: Span { start, end },
            }
        })
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
                Expr::Tuple(seq)
            } else {
                Expr::Paren(Box::new(ex))
            }
        } else {
            Expr::Tuple(Sequence {
                items: vec![],
                trailing: false,
            })
        };
        // ')'
        let end = self.expect_matching(&start_tok, TokenKind::RightParen)?;

        if peek!(self, TokenKind::FatArrow) {
            // closure expression!
            let args = match kind {
                Expr::Tuple(seq) => seq,
                Expr::Paren(ex) => Sequence {
                    items: vec![*ex],
                    trailing: false,
                },
                _ => unreachable!(),
            };
            return self.parse_closure_expr_with_seq(args, false, None, Span { start, end }, &ctx);
        }

        Ok(self.mk_expr(kind, Span { start, end }))
    }

    pub(crate) fn parse_name_seq(
        &mut self,
        trail: Trailing,
        ctx: &ParseContext,
    ) -> ParseResult<(Vec<Name>, Span)> {
        let mut names = vec![];
        let mut start = Pos::new();
        let mut end: Pos;
        loop {
            let n = self.parse_name_with_type()?;
            if start.empty() {
                start = n.span.start;
            }
            end = n.span.end;
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
    ) -> ParseResult<Sequence<SourceInfo>> {
        let mut items = vec![];
        let mut trailing = false;
        loop {
            match (vkind, self.must_peek_kind()?, &stop_token) {
                (_, k, Some(t)) if &k == t => break,
                (ValueKind::LValue, TokenKind::Identifier(_), _) => {
                    let n = self.parse_name_with_type()?;
                    let span = n.span;
                    items.push(self.mk_expr(Expr::Name(n), span))
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
        args: Sequence<SourceInfo>,
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
                let body = Box::new(self.mk_expr(Expr::Tuple(Sequence::empty()), span));
                return Ok(self.mk_expr(
                    Expr::Closure(Closure {
                        args: Sequence::empty(),
                        arrow_span: None,
                        curly_spans,
                        body,
                    }),
                    span,
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
            let name_span = name.span;
            if !has_curly {
                span.start = name_span.start;
            }

            span.end = name_span.end;
            Sequence {
                items: vec![self.mk_expr(Expr::Name(name), name_span)],
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
            Expr::Block(Block {
                stmts,
                is_top_level: ctx.top_level,
            }),
            Span { start, end },
        ))
    }
}
