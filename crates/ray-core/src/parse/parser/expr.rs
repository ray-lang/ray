use ray_shared::{
    pathlib::Path,
    span::{Span, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::TyScheme;

use crate::ast::{
    Boxed, Call, Curly, CurlyElement, Dot, Expr, FString, FStringPart, Index, Literal, Modifier,
    Name, New, Node, ScopedAccess, Sequence, TrailingPolicy, ValueKind,
    token::{Token, TokenKind},
};
use crate::parse::{
    lexer::{FStringSegment, NewlineMode},
    parser::Recover,
};

use super::{
    ExprResult, ParsedExpr, Parser, RecoveryCtx, Restrictions,
    context::{ParseContext, SeqSpec},
};

impl Parser<'_> {
    fn peek_double_colon_after_brackets(&mut self, max_lookahead: usize) -> bool {
        if !matches!(self.peek_kind(), TokenKind::LeftBracket) {
            return false;
        }

        let mut depth: usize = 0;
        for i in 0..max_lookahead {
            match self.peek_kind_at(i) {
                TokenKind::LeftBracket => depth += 1,
                TokenKind::RightBracket => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                    if depth == 0 {
                        return matches!(self.peek_kind_at(i + 1), TokenKind::DoubleColon);
                    }
                }
                TokenKind::EOF => return false,
                _ => {}
            }
        }

        false
    }

    pub(crate) fn parse_labeled_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse labeled expression");
        let ctx = &parser.ctx_clone();

        let name = parser.parse_name(ctx)?;
        let lhs_span = parser.srcmap.span_of(&name);
        let lhs = parser.mk_expr(Expr::Name(name.value), lhs_span, ctx.path.clone());

        if !peek!(parser, TokenKind::Colon) {
            return Ok(lhs);
        }

        parser.expect_sp(TokenKind::Colon, ctx)?;

        let mut rhs_ctx = ctx.clone();
        rhs_ctx.stop_token = Some(TokenKind::Comma);
        let rhs = parser.parse_expr(&rhs_ctx)?;

        let span = lhs_span.extend_to(&parser.srcmap.span_of(&rhs));
        Ok(parser.mk_expr(
            Expr::Labeled(Box::new(lhs), Box::new(rhs)),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let suppress_newlines = ctx.restrictions.contains(Restrictions::IN_PAREN);
        let mut parser = self.with_scope(ctx).with_description("parse expression");
        if suppress_newlines {
            parser = parser.with_newline_mode(NewlineMode::Suppress);
        }

        let ctx = &parser.ctx_clone();
        parser.parse_infix_expr(0, None, &ctx)
    }

    pub(crate) fn parse_base_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        match self.must_peek_kind()? {
            TokenKind::If => self.parse_if(ctx),
            TokenKind::For => self.parse_for(ctx),
            TokenKind::While => self.parse_while(ctx),
            TokenKind::Loop => self.parse_loop(ctx),
            TokenKind::Modifier(Modifier::Unsafe) => self.parse_unsafe_expr(ctx),
            TokenKind::New => self.parse_new_expr(ctx),
            TokenKind::Bx => self.parse_box_expr(ctx),
            TokenKind::Break => {
                let break_span = self.expect_keyword(TokenKind::Break, ctx)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = break_span.extend_to(&self.srcmap.span_of(&ex));
                    (Some(Box::new(ex)), span)
                } else {
                    (None, break_span)
                };
                Ok(self.mk_expr(Expr::Break(ex), span, ctx.path.clone()))
            }
            TokenKind::Continue => {
                let span = self.expect_keyword(TokenKind::Continue, ctx)?;
                Ok(self.mk_expr(Expr::Continue, span, ctx.path.clone()))
            }
            TokenKind::Return => {
                let return_span = self.expect_keyword(TokenKind::Return, ctx)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = return_span.extend_to(&self.srcmap.span_of(&ex));
                    (Some(Box::new(ex)), span)
                } else {
                    (None, return_span)
                };
                Ok(self.mk_expr(Expr::Return(ex), span, ctx.path.clone()))
            }
            TokenKind::Fn | TokenKind::Modifier(_) => self
                .parse_fn(false, ctx)
                .map(|(f, span)| self.mk_expr(Expr::Func(f), span, ctx.path.clone())),
            TokenKind::LeftParen => self.parse_paren_expr(ctx),
            TokenKind::LeftCurly => self.parse_curly_braced_expr(ctx),
            TokenKind::Mut => self.parse_local(false, ctx),
            TokenKind::Hash => {
                let span = self.expect_sp(TokenKind::Hash, ctx)?;
                self.parse_curly_expr(None, span, ctx)
            }
            TokenKind::DoubleQuote => {
                let (s, span) = self.expect_string(ctx)?;
                Ok(self.mk_expr(Expr::Literal(Literal::String(s)), span, ctx.path.clone()))
            }
            TokenKind::SingleQuote => {
                let (char_string, span) = self.expect_char(ctx)?;
                let ch = char_string.chars().next().unwrap();
                Ok(self.mk_expr(Expr::Literal(Literal::Char(ch)), span, ctx.path.clone()))
            }
            TokenKind::Identifier(s)
                if &s == "b"
                    && matches!(
                        self.peek_kind_at(1),
                        TokenKind::SingleQuote | TokenKind::DoubleQuote
                    ) =>
            {
                // parse the `b`
                let (_, Span { start, .. }) = self.expect_id(ctx)?;
                let quote = self.token()?;
                if quote.kind == TokenKind::SingleQuote {
                    let (char_string, Span { end, .. }) = self.expect_char(ctx)?;
                    let ch = char_string.chars().next().unwrap();
                    Ok(self.mk_expr(
                        Expr::Literal(Literal::Char(ch)),
                        Span { start, end },
                        ctx.path.clone(),
                    ))
                } else {
                    let (s, Span { end, .. }) = self.expect_string(ctx)?;
                    Ok(self.mk_expr(
                        Expr::Literal(Literal::String(s)),
                        Span { start, end },
                        ctx.path.clone(),
                    ))
                }
            }
            TokenKind::Identifier(s)
                if &s == "f" && matches!(self.peek_kind_at(1), TokenKind::DoubleQuote) =>
            {
                self.parse_fstring(ctx)
            }
            TokenKind::Identifier(_) | TokenKind::Underscore => {
                let n = self.parse_name(ctx)?;
                if peek!(self, TokenKind::FatArrow) {
                    // closure expression
                    let span = self.srcmap.span_of(&n);
                    let args = Sequence {
                        items: vec![self.mk_expr(Expr::Name(n.value), span, ctx.path.clone())],
                        trailing: false,
                    };
                    return self.parse_closure_expr_with_seq(args, false, None, span, ctx);
                }

                // Type-qualified scoped access: `T[...]::member`
                if peek!(self, TokenKind::LeftBracket) && self.peek_double_colon_after_brackets(256)
                {
                    let base_span = self.srcmap.span_of(&n);
                    let ty = self.parse_ty_with_name(n.value.to_string(), base_span, ctx)?;
                    let sep_tok = self.expect(TokenKind::DoubleColon, ctx)?;

                    let mut member_ctx = ctx.clone();
                    member_ctx.restrictions |= Restrictions::ALLOW_KEYWORD_NAMES;
                    let rhs = self.parse_name(&member_ctx)?;
                    let rhs_span = self.srcmap.span_of(&rhs);
                    let span = base_span.extend_to(&rhs_span);
                    let lhs = self.mk_expr(Expr::Type(ty), base_span, ctx.path.clone());
                    return Ok(self.mk_expr(
                        Expr::ScopedAccess(ScopedAccess {
                            lhs: Box::new(lhs),
                            rhs,
                            sep: sep_tok,
                        }),
                        span,
                        ctx.path.clone(),
                    ));
                }

                if expect_if!(self, TokenKind::DoubleColon) {
                    // Create the first segment node from the Name
                    let first_span = self.srcmap.span_of(&n);
                    let first_segment =
                        self.mk_node(n.value.to_string(), first_span, ctx.path.clone());
                    let segments = self.parse_expr_path_segments(first_segment, ctx)?;
                    // Calculate total span from first to last segment
                    let last_span = self.srcmap.span_of(segments.last().unwrap());
                    let span = Span {
                        start: first_span.start,
                        end: last_span.end,
                    };
                    Ok(self.mk_expr(Expr::Path(segments), span, ctx.path.clone()))
                } else {
                    let span = self.srcmap.span_of(&n);
                    Ok(self.mk_expr(Expr::Name(n.value), span, ctx.path.clone()))
                }
            }
            TokenKind::LeftBracket => self.parse_array_expr(ctx),
            _ => self.parse_atom(ctx),
        }
    }

    pub(crate) fn parse_postfix_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let base = self.parse_base_expr(ctx)?;
        self.parse_postfix_expr_with(base, ctx)
    }

    pub(crate) fn parse_postfix_expr_with(
        &mut self,
        mut ex: ParsedExpr,
        ctx: &ParseContext,
    ) -> ExprResult {
        loop {
            if let Some(tok) = self.expect_if_operator(TokenKind::Dot)? {
                // expr.member
                ex = self.parse_dot_expr(ex, tok, ctx)?;
                continue;
            }

            if peek!(self, TokenKind::DoubleColon) {
                // expr::member
                let sep_tok = self.expect(TokenKind::DoubleColon, ctx)?;
                let mut member_ctx = ctx.clone();
                member_ctx.restrictions |= Restrictions::ALLOW_KEYWORD_NAMES;
                let rhs = match self.parse_name(&member_ctx) {
                    Ok(name) => name,
                    Err(err) => {
                        // Error recovery: emit a ScopedAccess node with an empty-name
                        // RHS so that downstream consumers (e.g. completion) can
                        // still detect `Point::`.
                        self.record_parse_error(err);
                        let sep_end = sep_tok.span.end;
                        self.mk_node(Name::new(""), Span::at(sep_end), ctx.path.clone())
                    }
                };
                let start = self.srcmap.span_of(&ex).start;
                let end = self.srcmap.span_of(&rhs).end;
                ex = self.mk_expr(
                    Expr::ScopedAccess(ScopedAccess {
                        lhs: Box::new(ex),
                        rhs,
                        sep: sep_tok,
                    }),
                    Span { start, end },
                    ctx.path.clone(),
                );
                continue;
            }

            if peek!(self, TokenKind::LeftParen) {
                // expr(...)
                ex = self.parse_fn_call_expr(ex, &ctx)?;
                continue;
            }

            // If we have `pkg::foo::Bar[T]::method`, then after parsing `pkg::foo::Bar` as a Path
            // expression, we must treat `[T]` as type parameters (not indexing) when it is
            // immediately followed by `::`.
            if peek!(self, TokenKind::LeftBracket)
                && matches!(&ex.value, Expr::Path(_))
                && self.peek_double_colon_after_brackets(256)
            {
                let base_span = self.srcmap.span_of(&ex);
                let Expr::Path(segments) = &ex.value else {
                    unreachable!()
                };

                // Convert Vec<Node<String>> to ItemPath string
                let path_str = segments
                    .iter()
                    .map(|s| s.value.as_str())
                    .collect::<Vec<_>>()
                    .join("::");

                let ty_params = self.parse_ty_params(ctx)?;
                let mut synth_ids = vec![];
                let mut end = base_span.end;
                let tys = if let Some(ty_params) = ty_params {
                    end = ty_params.rb_span.end;
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

                let base_synth_id = self.mk_synthetic(base_span);
                synth_ids.insert(0, base_synth_id);

                let mut parsed_ty = Parsed::new(
                    TyScheme::from_mono(Ty::with_tys(path_str.as_str(), tys)),
                    self.mk_src(Span {
                        start: base_span.start,
                        end,
                    }),
                );
                parsed_ty.set_synthetic_ids(synth_ids);

                ex = self.mk_expr(
                    Expr::Type(parsed_ty),
                    Span {
                        start: base_span.start,
                        end,
                    },
                    ctx.path.clone(),
                );

                continue;
            }

            if peek!(self, TokenKind::LeftBracket) {
                // expr[...]
                ex = self.parse_index_expr(ex, ctx)?;
                continue;
            }

            if peek!(self, TokenKind::LeftCurly)
                && !ctx.restrictions.contains(Restrictions::NO_CURLY_EXPR)
            {
                // expr { ... }
                let begin = self.srcmap.span_of(&ex);
                ex = self.parse_curly_expr(Some(ex), begin, ctx)?;
                continue;
            }

            return Ok(ex);
        }
    }

    pub(crate) fn parse_unsafe_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parsing an unsafe expression");
        let ctx = &parser.ctx_clone();

        let tok = parser.token()?;
        if !matches!(tok.kind, TokenKind::Modifier(Modifier::Unsafe)) {
            return Err(parser.unexpected_token(&tok, "`unsafe`", ctx));
        }

        let start = tok.span.start;
        let ex = parser.parse_expr(ctx)?;
        let end = parser.srcmap.span_of(&ex).end;

        Ok(parser.mk_expr(
            Expr::Unsafe(Box::new(ex)),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_dot_expr(
        &mut self,
        lhs: ParsedExpr,
        dot_tok: Token,
        ctx: &ParseContext,
    ) -> ExprResult {
        let start = self.srcmap.span_of(&lhs).start;
        let mut member_ctx = ctx.clone();
        member_ctx.restrictions |= Restrictions::ALLOW_KEYWORD_NAMES;
        let rhs = match self.parse_name_with_type(None, &member_ctx) {
            Ok(name) => name,
            Err(err) => {
                // Error recovery: emit a Dot node with an empty-name RHS so that
                // downstream consumers (e.g. completion) can still detect `x.`.
                self.record_parse_error(err);
                let dot_end = dot_tok.span.end;
                self.mk_node(Name::new(""), Span::at(dot_end), ctx.path.clone())
            }
        };
        let end = self.srcmap.span_of(&rhs).end;
        Ok(self.mk_expr(
            Expr::Dot(Dot {
                lhs: Box::new(lhs),
                rhs,
                dot: dot_tok,
            }),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_fn_call_expr(&mut self, lhs: ParsedExpr, ctx: &ParseContext) -> ExprResult {
        let start = self.srcmap.span_of(&lhs).start;

        let (expects_type, is_some_ctor) = if let Expr::Name(n) = &lhs.value {
            match n.to_string().as_str() {
                "sizeof" => (true, false),
                "some" => (false, true),
                _ => (false, false),
            }
        } else {
            (false, false)
        };

        let paren_spec = SeqSpec {
            delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let (mut args, spans) =
            self.parse_delimited_seq(paren_spec, ctx, |parser, trailing, stop, ctx| {
                if expects_type {
                    if peek!(parser, TokenKind::RightParen) {
                        let span = parser.expect(TokenKind::RightParen, ctx)?.span;
                        return Err(parser.parse_error(
                            str!("expected type but found `)`"),
                            span,
                            ctx,
                        ));
                    }
                    let ty_scheme = parser.parse_type_annotation(Some(&TokenKind::RightParen), ctx);
                    let span = ty_scheme.span().unwrap().clone();
                    let seq = Sequence {
                        items: vec![parser.mk_expr(Expr::Type(ty_scheme), span, ctx.path.clone())],
                        trailing: false,
                    };
                    Ok(seq)
                } else {
                    parser.parse_expr_seq(ValueKind::RValue, trailing, stop, ctx)
                }
            })?;

        let (l_span, r_span) = spans.expect("function call should have paren spans");
        let paren_span = l_span.extend_to(&r_span);

        let args_span = if let (Some(first), Some(last)) = (args.items.first(), args.items.last()) {
            let first_span = self.srcmap.span_of(first);
            let last_span = self.srcmap.span_of(last);
            Span {
                start: first_span.start,
                end: last_span.end,
            }
        } else {
            Span {
                start: l_span.end,
                end: r_span.start,
            }
        };

        let mut end = paren_span.end;

        if !ctx.restrictions.contains(Restrictions::NO_CURLY_EXPR)
            && peek!(self, TokenKind::LeftCurly)
        {
            let closure = self.parse_closure_expr(ctx)?;
            end = self.srcmap.span_of(&closure).end;
            args.items.push(closure);
        }

        if is_some_ctor {
            // `some(expr)` is special syntax; require exactly one argument.
            if args.items.len() == 1 {
                let inner = args.items.pop().unwrap();
                return Ok(self.mk_expr(
                    Expr::Some(Box::new(inner)),
                    Span { start, end },
                    ctx.path.clone(),
                ));
            }
            // Arity mismatch: fall back to a normal call and let typechecking complain.
        }

        Ok(self.mk_expr(
            Expr::Call(Call {
                callee: Box::new(lhs),
                args,
                args_span,
                paren_span,
            }),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_index_expr(&mut self, lhs: ParsedExpr, ctx: &ParseContext) -> ExprResult {
        // Parse the contents with sequence-aware recovery
        let seq_spec = SeqSpec {
            delimiters: Some((TokenKind::LeftBracket, TokenKind::RightBracket)),
            trailing: TrailingPolicy::Forbid,
            newline: NewlineMode::Suppress,
            restrictions: ctx.restrictions,
        };

        let (seq, spans) =
            self.parse_delimited_seq(seq_spec, ctx, |parser, trailing, stop, ctx| {
                parser.parse_expr_seq(ValueKind::RValue, trailing, stop, ctx)
            })?;

        let (lbrack_span, rbrack_span) = spans.unwrap();

        let bracket_span = lbrack_span.extend_to(&rbrack_span);
        let span = self.srcmap.span_of(&lhs).extend_to(&rbrack_span);

        // Choose the index expression:
        //  - 0 items  -> Missing expression
        //  - 1 item   -> that item
        //  - >1 items -> keep them as a Sequence to preserve tokens
        let index_expr = match seq.items.len() {
            0 => self.missing_expr(lbrack_span.start, rbrack_span.end, ctx),
            1 => seq.items.into_iter().next().unwrap(),
            _ => {
                let idx_span = Span {
                    start: lbrack_span.end,
                    end: rbrack_span.start,
                };
                self.mk_expr(Expr::Sequence(seq), idx_span, ctx.path.clone())
            }
        };

        Ok(self.mk_expr(
            Expr::Index(Index {
                lhs: Box::new(lhs),
                index: Box::new(index_expr),
                bracket_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_curly_expr(
        &mut self,
        lhs: Option<ParsedExpr>,
        begin: Span,
        ctx: &ParseContext,
    ) -> ExprResult {
        let lhs = if let Some(lhs) = lhs {
            let span = self.srcmap.span_of(&lhs);
            let node_id = lhs.id;
            match lhs.value {
                Expr::Name(n) => Some(Node::with_id(node_id, n.path)),
                Expr::Path(segments) => {
                    let parts: Vec<String> = segments.into_iter().map(|s| s.value).collect();
                    Some(Node::with_id(node_id, Path::from(parts)))
                }
                _ => {
                    return Err(self.parse_error(
                        str!("expected identifier for struct expression"),
                        span,
                        ctx,
                    ));
                }
            }
        } else {
            None
        };

        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftCurly, TokenKind::RightCurly)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::empty(),
        };

        let (seq, spans) = self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
            parser
                .parse_sep_seq(
                    &TokenKind::Comma,
                    trailing,
                    stop.as_ref(),
                    ctx,
                    |parser, ctx| {
                        while matches!(parser.peek_kind(), TokenKind::NewLine) {
                            let _ = parser.token()?;
                        }
                        let kind = parser.peek_kind();
                        if !matches!(kind, TokenKind::Identifier(_)) && !kind.is_keyword_name() {
                            let tok = parser.peek();
                            return Err(parser.unexpected_token(
                                &tok,
                                "identifier or labeled expression",
                                ctx,
                            ));
                        }
                        let mut label_ctx = ctx.clone();
                        label_ctx.restrictions |= Restrictions::ALLOW_KEYWORD_NAMES;
                        label_ctx.stop_token = stop.clone();
                        parser.parse_labeled_expr(&label_ctx)
                    },
                )
                .map(|(items, trailing)| Sequence { items, trailing })
        })?;
        let (lcurly_span, rcurly_span) = spans.expect("curly expression requires braces");

        let mut elements = vec![];
        for item in seq.items {
            let span = self.srcmap.span_of(&item);
            let el = match item.value {
                Expr::Name(n) => CurlyElement::Name(n),
                Expr::Labeled(label, ex) => {
                    let label = match label.value {
                        Expr::Name(n) => n,
                        _ => return Err(
                            self.parse_error(
                                format!("expected name for label in curly expression, but found {}", label.value.desc()), 
                                self.srcmap.span_of(&label),
                                ctx,
                            )
                        ),
                    };

                    CurlyElement::Labeled(label, *ex)
                },
                _ => return Err(
                    self.parse_error(
                        format!("expected identifier or labeled expression in curly expression, but found {}", item.value.desc()), 
                        span,
                        ctx,
                    ),
                ),
            };

            elements.push(Node {
                id: item.id,
                value: el,
            });
        }

        let curly_span = lcurly_span.extend_to(&rcurly_span);
        let span = begin.extend_to(&rcurly_span);
        Ok(self.mk_expr(
            Expr::Curly(Curly {
                lhs,
                elements,
                curly_span,
                ty: TyScheme::default(),
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_new_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse new expression");
        let ctx = &parser.ctx_clone();

        let new_span = parser.expect_keyword(TokenKind::New, ctx)?;

        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftParen, TokenKind::RightParen)),
            trailing: TrailingPolicy::Forbid,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let ((parsed_ty, count), spans) =
            parser.parse_delimited_seq(spec, ctx, |parser, _, stop, ctx| {
                let ty = parser
                    .parse_type_annotation(stop.as_ref(), ctx)
                    .map(|t| t.into_mono());

                let count = if expect_if!(parser, TokenKind::Comma) {
                    let count_start = parser.lex.position();
                    let expr = parser.parse_expr(ctx).recover_with_ctx(
                        parser,
                        RecoveryCtx::expr(stop.as_ref()).with_ternary_sensitive(false),
                        |parser, recovered| parser.missing_expr(count_start, recovered, ctx),
                    );
                    Some(Box::new(expr))
                } else {
                    None
                };

                Ok((ty, count))
            })?;

        let (lparen_span, rparen_span) = spans.expect("new expression requires parentheses");
        let ty = parser.mk_ty(parsed_ty, ctx.path.clone());
        let paren_span = lparen_span.extend_to(&rparen_span);
        let span = new_span.extend_to(&rparen_span);
        Ok(parser.mk_expr(
            Expr::New(New {
                ty,
                count,
                new_span,
                paren_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_box_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse box expression");
        let ctx = &parser.ctx_clone();

        let box_span = parser.expect_keyword(TokenKind::Bx, ctx)?;

        let inner = parser.parse_expr(ctx)?;
        let inner_span = parser.srcmap.span_of(&inner);

        let span = box_span.extend_to(&inner_span);
        Ok(parser.mk_expr(
            Expr::Boxed(Boxed {
                inner: Box::new(inner),
                box_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    fn parse_fstring(&mut self, ctx: &ParseContext) -> ExprResult {
        let parser = &mut self.with_scope(ctx).with_description("parse f-string");
        let ctx = &parser.ctx_clone();

        // consume the `f` identifier
        let (_, Span { start, .. }) = parser.expect_id(ctx)?;
        // consume the opening `"`
        parser.expect_sp(TokenKind::DoubleQuote, ctx)?;

        let mut parts = Vec::new();
        loop {
            match parser.lex.next_fstring_segment('"') {
                FStringSegment::Literal(s) => {
                    parts.push(FStringPart::Literal(s));
                }
                FStringSegment::ExprStart => {
                    parser.lex.commit_position();
                    let mut expr_ctx = ctx.clone();
                    expr_ctx.stop_token = Some(TokenKind::RightCurly);
                    let expr = parser.parse_expr(&expr_ctx)?;
                    parser.expect_sp(TokenKind::RightCurly, ctx)?;
                    parts.push(FStringPart::Expr(expr));
                }
                FStringSegment::End => {
                    parser.lex.commit_position();
                    break;
                }
                FStringSegment::Unterminated => {
                    let end = parser.lex.position();
                    return Err(
                        parser.unexpected_eof(end, "unterminated f-string literal".to_string())
                    );
                }
            }
        }

        let end = parser.lex.position();
        let span = Span { start, end };
        Ok(parser.mk_expr(Expr::FString(FString { parts }), span, ctx.path.clone()))
    }
}
