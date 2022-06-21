use std::convert::TryFrom;

use super::{ExprResult, ParseContext, ParsedExpr, Parser, Restrictions};

use crate::{
    ast::{
        asm::{Asm, AsmOp, AsmOperand},
        token::{Token, TokenKind},
        Call, Curly, CurlyElement, Dot, Expr, Index, Literal, Modifier, New, Node, Sequence,
        Trailing, ValueKind,
    },
    span::{parsed::Parsed, Span},
    typing::ty::{SigmaTy, Ty, TyScheme},
};

impl Parser<'_> {
    pub(crate) fn parse_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let ex = self.parse_infix_expr(0, None, ctx)?;
        Ok(ex)
    }

    pub(crate) fn parse_base_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        match self.must_peek_kind()? {
            TokenKind::If => self.parse_if(ctx),
            TokenKind::For => self.parse_for(ctx),
            TokenKind::While => self.parse_while(ctx),
            TokenKind::Loop => self.parse_loop(ctx),
            TokenKind::Modifier(Modifier::Unsafe) => self.parse_unsafe_expr(ctx),
            TokenKind::Asm => self.parse_asm(ctx),
            TokenKind::New => self.parse_new_expr(ctx),
            TokenKind::Break => {
                let span = self.expect_sp(TokenKind::Break)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = span.extend_to(&self.srcmap.span_of(&ex));
                    (Some(Box::new(ex)), span)
                } else {
                    (None, span)
                };
                Ok(self.mk_expr(Expr::Break(ex), span, ctx.path.clone()))
            }
            TokenKind::Return => {
                let span = self.expect_sp(TokenKind::Return)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = span.extend_to(&self.srcmap.span_of(&ex));
                    (Some(Box::new(ex)), span)
                } else {
                    (None, span)
                };
                Ok(self.mk_expr(Expr::Return(ex), span, ctx.path.clone()))
            }
            TokenKind::Fn | TokenKind::Modifier(_) => self
                .parse_fn(false, ctx)
                .map(|(f, span)| self.mk_expr(Expr::Func(f), span, ctx.path.clone())),
            TokenKind::LeftParen => self.parse_paren_expr(ctx),
            TokenKind::LeftCurly => self.parse_block(ctx),
            TokenKind::Mut => self.parse_local(false, ctx),
            TokenKind::Hash => {
                let span = self.expect_sp(TokenKind::Hash)?;
                self.parse_curly_expr(None, span, ctx)
            }
            TokenKind::DoubleQuote => {
                let (s, span) = self.expect_string()?;
                Ok(self.mk_expr(Expr::Literal(Literal::String(s)), span, ctx.path.clone()))
            }
            TokenKind::SingleQuote => {
                let (char_string, span) = self.expect_char()?;
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
                let (_, Span { start, .. }) = self.expect_id()?;
                let quote = self.token()?;
                if quote.kind == TokenKind::SingleQuote {
                    let (char_string, Span { end, .. }) = self.expect_char()?;
                    let ch = char_string.chars().next().unwrap();
                    Ok(self.mk_expr(
                        Expr::Literal(Literal::Char(ch)),
                        Span { start, end },
                        ctx.path.clone(),
                    ))
                } else {
                    let (s, Span { end, .. }) = self.expect_string()?;
                    Ok(self.mk_expr(
                        Expr::Literal(Literal::String(s)),
                        Span { start, end },
                        ctx.path.clone(),
                    ))
                }
            }
            TokenKind::Identifier(_) | TokenKind::Struct | TokenKind::Underscore => {
                let n = self.parse_name()?;
                if peek!(self, TokenKind::FatArrow) {
                    // closure expression
                    let span = self.srcmap.span_of(&n);
                    let args = Sequence {
                        items: vec![self.mk_expr(Expr::Name(n.value), span, ctx.path.clone())],
                        trailing: false,
                    };
                    return self.parse_closure_expr_with_seq(args, false, None, span, ctx);
                }

                if expect_if!(self, TokenKind::DoubleColon) {
                    let p = self.parse_path_with((n.value.to_string(), self.srcmap.span_of(&n)))?;
                    let span = self.srcmap.span_of(&p);
                    Ok(self.mk_expr(Expr::Path(p.value), span, ctx.path.clone()))
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
            if let Some(tok) = self.expect_kind(TokenKind::Dot)? {
                // expr.member
                ex = self.parse_dot_expr(ex, tok, ctx)?;
                continue;
            }

            if let Some(tok) = self.expect_kind(TokenKind::LeftParen)? {
                // expr(...)
                let mut ctx = ctx.clone();
                ctx.restrictions |= Restrictions::IN_PAREN;
                ex = self.parse_fn_call_expr(ex, tok, &ctx)?;
                continue;
            }

            if let Some(tok) = self.expect_kind(TokenKind::LeftBracket)? {
                // expr[...]
                ex = self.parse_index_expr(ex, tok, ctx)?;
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
        let tok = self.token()?;
        if !matches!(tok.kind, TokenKind::Modifier(Modifier::Unsafe)) {
            return Err(self.unexpected_token(&tok, "`unsafe`"));
        }

        let start = tok.span.start;
        let ex = self.parse_expr(ctx)?;
        let end = self.srcmap.span_of(&ex).end;

        Ok(self.mk_expr(
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
        let rhs = self.parse_name_with_type()?;
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

    pub(crate) fn parse_fn_call_expr(
        &mut self,
        lhs: ParsedExpr,
        lparen_tok: Token,
        ctx: &ParseContext,
    ) -> ExprResult {
        let start = self.srcmap.span_of(&lhs).start;

        let expects_type = if let Expr::Name(n) = &lhs.value {
            match n.to_string().as_str() {
                "sizeof" => true,
                _ => false,
            }
        } else {
            false
        };

        let (mut args, args_span) = if !peek!(self, TokenKind::RightParen) {
            if expects_type {
                let ty = self.parse_ty()?;
                let span = *ty.span().unwrap();
                (
                    Sequence {
                        items: vec![self.mk_expr(Expr::Type(ty), span, ctx.path.clone())],
                        trailing: false,
                    },
                    span,
                )
            } else {
                let mut ctx = ctx.clone();
                ctx.stop_token = Some(TokenKind::RightParen);
                let args = self.parse_expr(&ctx)?;
                let span = self.srcmap.span_of(&args);
                (
                    if let Expr::Sequence(seq) = args.value {
                        seq
                    } else {
                        Sequence {
                            items: vec![args],
                            trailing: false,
                        }
                    },
                    span,
                )
            }
        } else if expects_type {
            let span = self.expect_sp(TokenKind::RightParen)?;
            return Err(self.parse_error(str!("expected type but found `)`"), span));
        } else {
            (
                Sequence {
                    items: vec![],
                    trailing: false,
                },
                Span {
                    start: lparen_tok.span.end,
                    end: self.lex.position(),
                },
            )
        };
        let rparen_end = self.expect_matching(&lparen_tok, TokenKind::RightParen)?;
        let mut end = rparen_end;

        if peek!(self, TokenKind::LeftCurly) {
            let closure = self.parse_closure_expr(ctx)?;
            end = self.srcmap.span_of(&closure).end;
            args.items.push(closure);
        }

        Ok(self.mk_expr(
            Expr::Call(Call {
                callee: Box::new(lhs),
                args,
                args_span,
                paren_span: Span {
                    start: lparen_tok.span.start,
                    end: rparen_end,
                },
            }),
            Span { start, end },
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_index_expr(
        &mut self,
        lhs: ParsedExpr,
        lbrack_tok: Token,
        ctx: &ParseContext,
    ) -> ExprResult {
        let index = self.parse_expr(ctx)?;
        let rbrack_span = self.expect_sp(TokenKind::RightBracket)?;
        let span = self.srcmap.span_of(&lhs).extend_to(&rbrack_span);
        Ok(self.mk_expr(
            Expr::Index(Index {
                lhs: Box::new(lhs),
                index: Box::new(index),
                bracket_span: lbrack_tok.span.extend_to(&rbrack_span),
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
            match lhs.value {
                Expr::Name(n) => Some(Parsed::new(n.path, self.mk_src(span))),
                _ => {
                    return Err(
                        self.parse_error(str!("expected identifier for struct expression"), span)
                    )
                }
            }
        } else {
            None
        };

        let lcurly_span = self.expect_sp(TokenKind::LeftCurly)?;

        let seq = self.parse_expr_seq(
            ValueKind::RValue,
            Trailing::Allow,
            Some(TokenKind::RightCurly),
            ctx,
        )?;

        let mut elements = vec![];
        for item in seq.items {
            let span = self.srcmap.span_of(&item);
            let el = match item.value {
                Expr::Name(n) => CurlyElement::Name(n),
                Expr::Labeled(label, ex) => {
                    let label = match label.value {
                        Expr::Name(n) => n,
                        _ => return Err(self.parse_error(format!("expected name for label in curly expression, but found {}", label.value.desc()), self.srcmap.span_of(&label))),
                    };

                    CurlyElement::Labeled(label, *ex)
                },
                _ => return Err(self.parse_error(format!("expected identifier or labeled expression in curly expression, but found {}", item.value.desc()), span)),
            };

            elements.push(Node {
                id: item.id,
                value: el,
            });
        }

        let rcurly_span = self.expect_sp(TokenKind::RightCurly)?;
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

    pub fn parse_new_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let new_span = self.expect_sp(TokenKind::New)?;
        let lparen_span = self.expect_sp(TokenKind::LeftParen)?;

        let parsed_ty = self.parse_ty()?.map(|t| t.into_mono());
        let ty = self.mk_ty(parsed_ty, ctx.path.clone());

        let count = if expect_if!(self, TokenKind::Comma) {
            Some(Box::new(self.parse_expr(ctx)?))
        } else {
            None
        };
        let rparen_span = self.expect_sp(TokenKind::RightParen)?;

        let paren_span = lparen_span.extend_to(&rparen_span);
        let span = new_span.extend_to(&rparen_span);
        Ok(self.mk_expr(
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

    pub(crate) fn parse_asm(&mut self, ctx: &ParseContext) -> ExprResult {
        let mut span = self.expect_sp(TokenKind::Asm)?;

        let mut inst = vec![];
        let ret_ty = if peek!(self, TokenKind::LeftParen) {
            self.expect(TokenKind::LeftParen)?;
            let t = self.parse_ty()?.map(|t| t.into_mono());
            self.expect(TokenKind::RightParen)?;
            Some(t)
        } else {
            None
        };

        self.expect(TokenKind::LeftCurly)?;
        while !peek!(self, TokenKind::RightCurly) {
            self.expect(TokenKind::Dollar)?;
            let (op, span) = self.expect_id()?;
            let op = match AsmOp::try_from(op.as_str()) {
                Ok(op) => op,
                Err(s) => {
                    return Err(self.parse_error(format!("invalid asm operator `${}`", s), span))
                }
            };

            let mut operands = vec![];
            loop {
                let kind = self.peek_kind();
                operands.push(match kind {
                    TokenKind::Identifier(_) => {
                        let (id, _) = self.expect_id()?;
                        AsmOperand::Var(id)
                    }
                    TokenKind::Integer { .. } => {
                        let tok = self.token()?;
                        let i = match tok.kind {
                            TokenKind::Integer { value, .. } => value.parse::<u64>()?,
                            _ => unreachable!(),
                        };
                        AsmOperand::Int(i)
                    }
                    _ => break,
                });
            }

            inst.push((op, operands));
        }

        span.end = self.expect_end(TokenKind::RightCurly)?;
        Ok(self.mk_expr(Expr::Asm(Asm { ret_ty, inst }), span, ctx.path.clone()))
    }
}
