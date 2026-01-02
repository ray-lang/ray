use std::convert::TryFrom;

use ray_shared::pathlib::Path;

use super::{
    DocComments, ExprResult, ParseResult, Parser, Recover, RecoveryCtx, Restrictions,
    context::ParseContext,
};

use crate::{
    ast::{
        Block, Closure, Expr, Literal, Missing, Name, Node, Pattern, Sequence, TrailingPolicy,
        Tuple, ValueKind, token::TokenKind,
    },
    parse::{lexer::NewlineMode, parser::context::SeqSpec},
};
use ray_shared::span::Span;

impl Parser<'_> {
    pub(crate) fn parse_atom(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parsing an atomic expression");

        let ctx = &parser.ctx_clone();

        let tok = parser.peek();
        match tok.kind {
            TokenKind::Integer { .. }
            | TokenKind::Float { .. }
            | TokenKind::Bool(..)
            | TokenKind::Nil => {
                let tok = parser.token()?;
                let span = tok.span;
                let fp = parser.options.filepath.clone();
                Ok(parser.mk_expr(
                    Expr::Literal(Literal::from_token(tok, fp, &ctx.path)?),
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
                let pos = parser.lex.position();
                log::debug!("expected expression but found {} at pos {}", tok, pos);
                Err(parser.unexpected_token(&tok, expected, ctx))
            }
        }
    }

    pub(crate) fn parse_path(&mut self, ctx: &ParseContext) -> ParseResult<Node<Path>> {
        let (id, span) = self.expect_id(ctx)?;
        if expect_if!(self, TokenKind::DoubleColon) {
            self.parse_path_with((id, span), ctx)
        } else {
            Ok(self.mk_node(Path::from(vec![id]), span, ctx.path.clone()))
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

        Ok(self.mk_node(Path::from(parts), span, ctx.path.clone()))
    }

    pub(crate) fn parse_pattern_with_stop(
        &mut self,
        stop: Option<&TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Node<Pattern>> {
        let parser = &mut self.with_scope(ctx).with_description("parse pattern");
        let ctx = &parser.ctx_clone();

        Ok(if peek!(parser, TokenKind::LeftParen) {
            parser.parse_paren_pattern(ctx)?
        } else {
            let start = parser.lex.position();
            let seq = parser.parse_expr_seq(
                // Use general expression parsing here and rely on
                // `Pattern::try_from` to reject invalid shapes.
                ValueKind::RValue,
                TrailingPolicy::Warn,
                stop.cloned(),
                ctx,
            )?;
            let end = parser.lex.position();
            let span = Span { start, end };
            if seq.items.len() == 0 {
                return Err(parser.parse_error(
                    "expected one or more items in pattern, but found none".to_string(),
                    span,
                    ctx,
                ));
            }

            let value = Pattern::try_from(seq).map_err(|mut e| {
                let src = parser.mk_src(span);
                e.src.push(src);
                e
            })?;

            parser.mk_node(value, span, ctx.path.clone())
        })
    }

    pub(crate) fn parse_name(&mut self, ctx: &ParseContext) -> ParseResult<Node<Name>> {
        let (name, span) = self.expect_id(ctx)?;
        Ok(self.mk_node(Name::new(name), span, ctx.path.clone()))
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

        Ok(self.mk_node(name, span, ctx.path.clone()))
    }

    pub(crate) fn parse_paren_pattern(&mut self, ctx: &ParseContext) -> ParseResult<Node<Pattern>> {
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        ctx.description = Some("parse paren pattern".to_string());

        let mut parser = self
            .with_scope(&ctx)
            .with_description("parsing paren pattern");
        let ctx = parser.ctx_clone();

        let (mut seq, delims) = parser.parse_delimited_seq(
            SeqSpec {
                delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
                trailing: TrailingPolicy::Allow,
                newline: NewlineMode::Suppress,
                restrictions: Restrictions::IN_PAREN,
            },
            &ctx,
            |parser, trailing, stop, ctx| {
                parser.parse_expr_seq(ctx.get_vkind(), trailing, stop, ctx)
            },
        )?;

        let (l_span, r_span) = delims.unwrap();
        let span = l_span.extend_to(&r_span);
        let pattern = if seq.items.len() == 1 && !seq.trailing {
            let item = seq.items.pop().unwrap();
            Pattern::try_from(item.value).map_err(|mut e| {
                let src = parser.mk_src(span);
                e.src.push(src);
                e
            })?
        } else {
            Pattern::tuple(seq).map_err(|mut e| {
                let src = parser.mk_src(span);
                e.src.push(src);
                e
            })?
        };

        Ok(parser.mk_node(pattern, span, ctx.path.clone()))
    }

    pub(crate) fn parse_paren_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse paren expression");
        let ctx = &parser.ctx_clone();

        // '('
        let start_tok = parser.expect(TokenKind::LeftParen, ctx)?;
        let start = start_tok.span.start;
        let mut ctx = ctx.clone();
        ctx.restrictions |= Restrictions::IN_PAREN;
        let kind = if !peek!(parser, TokenKind::RightParen) {
            ctx.stop_token = Some(TokenKind::RightParen);
            let ex = parser.parse_expr(&ctx)?;
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
        let end = parser.expect_matching(&start_tok, TokenKind::RightParen, &ctx)?;

        if peek!(parser, TokenKind::FatArrow) {
            // closure expression!
            let args = match kind {
                Expr::Tuple(tuple) => tuple.seq,
                Expr::Paren(ex) => Sequence {
                    items: vec![*ex],
                    trailing: false,
                },
                _ => unreachable!(),
            };
            return parser.parse_closure_expr_with_seq(
                args,
                false,
                None,
                Span { start, end },
                &ctx,
            );
        }

        Ok(parser.mk_expr(kind, Span { start, end }, ctx.path.clone()))
    }

    pub(crate) fn parse_expr_seq(
        &mut self,
        vkind: ValueKind,
        trail: TrailingPolicy,
        stop_token: Option<TokenKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Sequence> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse expression sequence")
            .with_newline_mode(NewlineMode::Suppress);
        let ctx = parser.ctx_clone();
        log::debug!(
            "[parser] parse_expr_seq: mode={:?} stop={:?} next={:?}",
            parser.lex.newline_mode(),
            stop_token,
            parser.peek_kind()
        );
        let stop_ref = stop_token.as_ref();
        let stop_token_for_expr = stop_token.clone();
        let seq_ctx = RecoveryCtx::default_seq(stop_ref)
            .with_trailing(trail)
            .with_newline(false);

        let (mut items, mut trailing) =
            parser.parse_sep_seq(&TokenKind::Comma, trail, stop_ref, &ctx, |parser, ctx| {
                match vkind {
                    ValueKind::LValue => {
                        if !matches!(parser.peek_kind(), TokenKind::Identifier(_)) {
                            let tok = parser.peek();
                            return Err(parser.unexpected_token(&tok, "identifier", ctx));
                        }
                        let name = parser.parse_name_with_type(stop_ref, ctx)?;
                        let span = parser.srcmap.span_of(&name);
                        Ok(parser.mk_expr(Expr::Name(name.value), span, ctx.path.clone()))
                    }
                    ValueKind::RValue => {
                        let mut elem_ctx = ctx.clone();
                        elem_ctx.stop_token = stop_token_for_expr.clone();
                        let expr = parser
                            .parse_expr(&elem_ctx)
                            .map(Some)
                            .recover_seq_with_ctx(parser, seq_ctx.clone(), |_| None)
                            .ok_or_else(|| {
                                let tok = parser.peek();
                                parser.unexpected_token(&tok, "expression", ctx)
                            })?;
                        Ok(expr)
                    }
                }
            })?;

        if let ValueKind::RValue = vkind {
            let mut flattened = Vec::with_capacity(items.len());
            let mut inner_trailing = false;
            for expr in items.drain(..) {
                if let Expr::Sequence(seq) = expr.value {
                    inner_trailing |= seq.trailing;
                    flattened.extend(seq.items);
                } else {
                    flattened.push(expr);
                }
            }
            items = flattened;
            trailing |= inner_trailing;
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
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parsing closure expression with sequence");
        let ctx = &parser.ctx_clone();

        let arrow_span = Some(parser.expect_sp(TokenKind::FatArrow, ctx)?);

        let body = parser.parse_expr(ctx)?;

        if has_curly {
            let r = parser.expect_sp(TokenKind::RightCurly, ctx)?;
            span.end = r.end;
            if let Some((l, _)) = curly_spans {
                curly_spans = Some((l, r));
            }
        }

        Ok(parser.mk_expr(
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
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse closure expression");
        let ctx = &parser.ctx_clone();

        let mut span = Span::new();
        let has_curly = peek!(parser, TokenKind::LeftCurly);
        let mut curly_spans = None;
        if has_curly {
            let l = parser.expect_sp(TokenKind::LeftCurly, ctx)?;
            span.start = l.start;

            // handle an empty closure
            if peek!(parser, TokenKind::RightCurly) {
                let r = parser.expect_sp(TokenKind::RightCurly, ctx)?;
                span.end = r.end;
                curly_spans = Some((l, r));
                let body = Box::new(parser.mk_expr(
                    Expr::Tuple(Tuple {
                        seq: Sequence::empty(),
                    }),
                    span,
                    ctx.path.clone(),
                ));
                return Ok(parser.mk_expr(
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

        let args = if peek!(parser, TokenKind::LeftParen) {
            let spec = SeqSpec {
                delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
                trailing: TrailingPolicy::Allow,
                newline: NewlineMode::Suppress,
                restrictions: Restrictions::IN_PAREN,
            };

            let (seq, spans) =
                parser.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                    parser.parse_expr_seq(ctx.get_vkind(), trailing, stop, ctx)
                })?;

            let (l_paren, r_paren) = spans.expect("closure arguments should have paren spans");
            if !has_curly {
                span.start = l_paren.start;
            }
            span.end = r_paren.end;
            seq
        } else {
            // single arg or underscore
            let name = parser.parse_name_with_type(None, ctx)?;
            let name_span = parser.srcmap.span_of(&name);
            if !has_curly {
                span.start = name_span.start;
            }

            span.end = name_span.end;
            Sequence {
                items: vec![parser.mk_expr(Expr::Name(name.value), name_span, ctx.path.clone())],
                trailing: false,
            }
        };

        parser.parse_closure_expr_with_seq(args, has_curly, curly_spans, span, ctx)
    }

    pub(crate) fn parse_block(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self.with_scope(ctx).with_description("parse block");
        let ctx = &parser.ctx_clone();

        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftCurly, TokenKind::RightCurly)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Emit,
            restrictions: Restrictions::empty(),
        };

        let (stmts, spans) = parser.parse_delimited_seq(spec, ctx, |parser, _, stop, ctx| {
            let stop_kind = stop.clone();
            let stop_ref = stop_kind.as_ref();
            let mut stmts = Vec::new();

            loop {
                log::debug!(
                    "[parser] parse_block loop: newline_mode={:?} next={:?} stop={:?}",
                    parser.lex.newline_mode(),
                    parser.peek_kind(),
                    stop_ref
                );
                if stop_ref
                    .map(|stop_tok| parser.peek_kind().similar_to(stop_tok))
                    .unwrap_or(false)
                {
                    log::debug!("[parser] parse_block: stopping before statement");
                    break;
                }

                let DocComments {
                    module: _,
                    item: doc,
                } = parser.parse_doc_comments();
                log::debug!(
                    "[parser] parse_block: after doc comments next={:?}",
                    parser.peek_kind()
                );

                while matches!(parser.peek_kind(), TokenKind::NewLine) {
                    log::debug!("[parser] parse_block: skipping newline");
                    parser.expect(TokenKind::NewLine, ctx)?;
                    if stop_ref
                        .map(|stop_tok| parser.peek_kind().similar_to(stop_tok))
                        .unwrap_or(false)
                    {
                        log::debug!(
                            "[parser] parse_block: stop after newline next={:?}",
                            parser.peek_kind()
                        );
                        break;
                    }
                }

                if stop_ref
                    .map(|stop_tok| parser.peek_kind().similar_to(stop_tok))
                    .unwrap_or(false)
                {
                    log::debug!("[parser] parse_block: stopping before stmt parse");
                    break;
                }

                let stmt_recovered = parser.parse_stmt(None, doc, ctx).recover_with_ctx_outcome(
                    parser,
                    RecoveryCtx::stmt(stop_ref)
                        .with_decl_stops(true)
                        .with_newline(true),
                    |parser, _outcome| {
                        let info = Missing::new("statement", Some(ctx.path.to_string()));
                        parser.mk_expr(Expr::Missing(info), Span::new(), ctx.path.clone())
                    },
                );
                let stmt = stmt_recovered.value;
                log::debug!(
                    "[parser] parse_block: parsed stmt kind={:?}",
                    stmt.value.desc()
                );

                if matches!(stmt.value, Expr::Missing(_))
                    && (stop_ref
                        .map(|stop_tok| parser.peek_kind().similar_to(stop_tok))
                        .unwrap_or(false)
                        || parser.is_eof())
                {
                    log::debug!("[parser] parse_block: missing stmt, breaking");
                    break;
                }

                stmts.push(stmt);

                if stop_ref
                    .map(|stop_tok| parser.peek_kind().similar_to(stop_tok))
                    .unwrap_or(false)
                {
                    log::debug!("[parser] parse_block: stopping after stmt");
                    break;
                }

                parser.expect_semi_or_eol(ctx)?;
                log::debug!(
                    "[parser] parse_block: after expect_semi_or_eol next={:?}",
                    parser.peek_kind()
                );
            }
            Ok(stmts)
        })?;

        let (l_span, r_span) = spans.expect("block should have braces");
        Ok(parser.mk_expr(
            Expr::Block(Block::new(stmts)),
            l_span.extend_to(&r_span),
            ctx.path.clone(),
        ))
    }
}
