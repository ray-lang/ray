use super::{ParseContext, ParseResult, Parser, Restrictions};

use crate::ast;
use crate::ast::token::{Token, TokenKind};
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let mut ex = self.parse_infix_expr(0, None, ctx)?;
        if peek!(self, TokenKind::If) {
            // expr if ... else ...
            ex = self.parse_ternary_expr(ex, ctx)?;
        }
        Ok(ex)
    }

    pub(crate) fn parse_base_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        match self.must_peek_kind()? {
            TokenKind::If => self.parse_if(ctx),
            TokenKind::For => self.parse_for(ctx),
            TokenKind::While => self.parse_while(ctx),
            TokenKind::Loop => self.parse_loop(ctx),
            TokenKind::Modifier(ast::Modifier::Unsafe) => self.parse_unsafe_expr(ctx),
            TokenKind::Break => {
                let span = self.expect_sp(TokenKind::Break)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = span.extend_to(&ex.span);
                    (Some(Box::new(ex)), span)
                } else {
                    (None, span)
                };
                Ok(self.mk_expr(ast::ExprKind::Break(ex), span))
            }
            TokenKind::Return => {
                let span = self.expect_sp(TokenKind::Return)?;
                let (ex, span) = if self.is_next_expr_begin() {
                    let ex = self.parse_expr(ctx)?;
                    let span = span.extend_to(&ex.span);
                    (Some(Box::new(ex)), span)
                } else {
                    (None, span)
                };
                Ok(self.mk_expr(ast::ExprKind::Return(ex), span))
            }
            TokenKind::Fn | TokenKind::Modifier(_) => self.parse_fn(false, ctx).map(|f| {
                let span = f.span;
                self.mk_expr(ast::ExprKind::Fn(f), span)
            }),
            TokenKind::LeftParen => self.parse_paren_expr(ctx),
            TokenKind::LeftCurly => self.parse_block(ctx),
            TokenKind::Mut => self.parse_local(false, ctx),
            TokenKind::Identifier(_) | TokenKind::Struct | TokenKind::Underscore => {
                let n = self.parse_name()?;
                if peek!(self, TokenKind::FatArrow) {
                    // closure expression
                    let span = n.span;
                    let args = ast::Sequence {
                        items: vec![self.mk_expr(ast::ExprKind::Name(n), span)],
                        trailing: false,
                    };
                    return self.parse_closure_expr_with_seq(args, false, None, span, ctx);
                }

                if expect_if!(self, TokenKind::DoubleColon) {
                    let p = self.parse_path_with((n.name, n.span))?;
                    let span = p.span;
                    Ok(self.mk_expr(ast::ExprKind::Path(p), span))
                } else {
                    let span = n.span;
                    Ok(self.mk_expr(ast::ExprKind::Name(n), span))
                }
            }
            TokenKind::LeftBracket => self.parse_array_expr(ctx),
            _ => self.parse_atom(ctx),
        }
    }

    pub(crate) fn parse_postfix_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let base = self.parse_base_expr(ctx)?;
        self.parse_postfix_expr_with(base, ctx)
    }

    pub(crate) fn parse_postfix_expr_with(
        &mut self,
        mut ex: ast::Expr,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        loop {
            if let Some(tok) = self.expect_kind(TokenKind::Dot)? {
                // expr.member
                ex = self.parse_dot_expr(ex, tok)?;
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

            if let Some(tok) = self.expect_kind(TokenKind::LeftCurly)? {
                // expr { ... }
                ex = self.parse_curly_expr(ex, tok, ctx)?;
                continue;
            }

            return Ok(ex);
        }
    }

    pub(crate) fn parse_unsafe_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        let tok = self.token()?;
        if !matches!(tok.kind, TokenKind::Modifier(ast::Modifier::Unsafe)) {
            return Err(self.unexpected_token(&tok, "`unsafe`"));
        }

        let start = tok.span.start;
        let ex = self.parse_expr(ctx)?;
        let end = ex.span.end;

        Ok(self.mk_expr(ast::ExprKind::Unsafe(Box::new(ex)), Span { start, end }))
    }

    pub(crate) fn parse_dot_expr(
        &mut self,
        lhs: ast::Expr,
        dot_tok: Token,
    ) -> ParseResult<ast::Expr> {
        let start = lhs.span.start;
        let rhs = self.parse_name_with_type()?;
        let end = rhs.span.end;
        Ok(self.mk_expr(
            ast::ExprKind::Dot(ast::Dot {
                lhs: Box::new(lhs),
                rhs,
                desugared: None,
                dot: dot_tok,
            }),
            Span { start, end },
        ))
    }

    pub(crate) fn parse_fn_call_expr(
        &mut self,
        mut lhs: ast::Expr,
        lparen_tok: Token,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let start = lhs.span.start;
        let mut ty_args = None;

        let expects_type = if let ast::ExprKind::Name(n) = &lhs.kind {
            match n.name.as_str() {
                "sizeof" => true,
                _ => false,
            }
        } else {
            false
        };

        if let ast::ExprKind::Index(idx) = lhs.kind {
            // convert this to type arguments
            let span = idx.index.span;
            if let Some(tys) = ast::Type::from_expr(&idx.index) {
                lhs = *idx.lhs;
                ty_args = Some((tys, span));
            } else {
                lhs = ast::Expr {
                    kind: ast::ExprKind::Index(idx),
                    span: lhs.span,
                    filepath: lhs.filepath,
                    doc: lhs.doc,
                    id: lhs.id,
                }
            }
        }

        let (mut args, args_span) = if !peek!(self, TokenKind::RightParen) {
            if expects_type {
                let ty = self.parse_ty()?;
                let span = ty.span.unwrap();
                (
                    ast::Sequence {
                        items: vec![self.mk_expr(ast::ExprKind::Type(ty), span)],
                        trailing: false,
                    },
                    span,
                )
            } else {
                let mut ctx = ctx.clone();
                ctx.stop_token = Some(TokenKind::RightParen);
                let args = self.parse_expr(&ctx)?;
                let span = args.span;
                (
                    if let ast::ExprKind::Sequence(seq) = args.kind {
                        seq
                    } else {
                        ast::Sequence {
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
                ast::Sequence {
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
            end = closure.span.end;
            args.items.push(closure);
        }

        Ok(self.mk_expr(
            ast::ExprKind::Call(ast::Call {
                lhs: Box::new(lhs),
                args,
                args_span,
                ty_args,
                paren_span: Span {
                    start: lparen_tok.span.start,
                    end: rparen_end,
                },
            }),
            Span { start, end },
        ))
    }

    pub(crate) fn parse_index_expr(
        &mut self,
        lhs: ast::Expr,
        lbrack_tok: Token,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let index = self.parse_expr(ctx)?;
        let rbrack_span = self.expect_sp(TokenKind::RightBracket)?;
        let span = lhs.span.extend_to(&rbrack_span);
        Ok(self.mk_expr(
            ast::ExprKind::Index(ast::Index {
                lhs: Box::new(lhs),
                index: Box::new(index),
                bracket_span: lbrack_tok.span.extend_to(&rbrack_span),
            }),
            span,
        ))
    }

    pub(crate) fn parse_curly_expr(
        &mut self,
        lhs: ast::Expr,
        lcurly_tok: Token,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let lhs = match lhs.kind {
            ast::ExprKind::Name(n) => n,
            _ => {
                return Err(
                    self.parse_error(str!("expected identifier for struct expression"), lhs.span)
                )
            }
        };

        let seq = self.parse_expr_seq(
            ast::ValueKind::RValue,
            ast::Trailing::Allow,
            Some(TokenKind::RightCurly),
            ctx,
        )?;
        let mut elements = vec![];
        for item in seq.items {
            let span = item.span;
            let kind = match item.kind {
                ast::ExprKind::Name(n) => ast::CurlyElementKind::Name(n),
                ast::ExprKind::Labeled(label, ex) => {
                    let label = match label.kind {
                        ast::ExprKind::Name(n) => n,
                        _ => return Err(self.parse_error(format!("expected name for label in curly expression, but found {}", label.kind.desc()), label.span)),
                    };

                    ast::CurlyElementKind::Labeled(label, *ex)
                },
                _ => return Err(self.parse_error(format!("expected identifier or labeled expression in curly expression, but found {}", item.kind.desc()), span)),
            };

            elements.push(ast::CurlyElement { kind, span })
        }
        let rcurly_span = self.expect_sp(TokenKind::RightCurly)?;
        let curly_span = lcurly_tok.span.extend_to(&rcurly_span);
        let span = lhs.span.extend_to(&rcurly_span);
        Ok(self.mk_expr(
            ast::ExprKind::Curly(ast::Curly {
                lhs,
                elements,
                curly_span,
            }),
            span,
        ))
    }
}
