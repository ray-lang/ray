use super::{ParseContext, ParseResult, Parser, Restrictions};

use crate::ast;
use crate::ast::token::TokenKind;
use crate::span::Span;

impl Parser {
    pub(crate) fn parse_infix_expr(
        &mut self,
        min_prec: usize,
        lhs: Option<ast::Expr>,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let mut lhs = if let Some(lhs) = lhs {
            lhs
        } else {
            self.parse_prefix_expr(ctx)?
        };

        let mut ctx = ctx.clone();
        while let Some((op, tok_count)) = self.peek_infix_op(&ctx)? {
            let prec = op.precedence();
            if prec < min_prec {
                break;
            }

            if op == ast::InfixOp::Else && ctx.restrictions.contains(Restrictions::IF_ELSE) {
                // handle the if .. else case
                // TODO: is there a case of `if .. else .. else`?
                break;
            }

            let (_, op_span) = self.lex.consume_count(tok_count);

            match (self.peek_kind(), &ctx.stop_token) {
                (k, Some(t)) if &k == t => {
                    if matches!(op, ast::InfixOp::Comma) {
                        if let ast::ExprKind::Sequence(seq) = &mut lhs.kind {
                            seq.trailing = true;
                        } else {
                            let span = lhs.span.extend_to(&op_span);
                            lhs = self.mk_expr(
                                ast::ExprKind::Sequence(ast::Sequence {
                                    items: vec![lhs],
                                    trailing: true,
                                }),
                                span,
                            )
                        }
                    }
                    break;
                }
                _ => (),
            };

            if op == ast::InfixOp::RangeInclusive || op == ast::InfixOp::RangeExclusive {
                lhs = self.parse_range_expr(prec, lhs, op, op_span, &ctx)?;
                break;
            }

            if op == ast::InfixOp::As {
                lhs = self.parse_cast_expr(lhs, op_span, &ctx)?;
                continue;
            }

            let associativity = op.associativity();
            let prec_adjustment = match associativity {
                ast::Associativity::Right => 0,
                ast::Associativity::Left | ast::Associativity::None => 1,
            };

            if matches!(op, ast::InfixOp::Assign | ast::InfixOp::AssignOp(_)) {
                ctx.restrictions |= Restrictions::ASSIGN;
                ctx.restrictions -= Restrictions::LVALUE;
            }

            if matches!(op, ast::InfixOp::Comma) {
                ctx = ctx.clone();
                ctx.restrictions |= Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA;
            } else if matches!(op, ast::InfixOp::Colon)
                && !matches!(lhs.kind, ast::ExprKind::Name(_))
            {
                // this is a typed expression
                let ty = self.parse_ty()?;
                let ty_span = ty.span.unwrap();
                let rhs = self.mk_expr(ast::ExprKind::Type(ty), ty_span);
                let span = lhs.span.extend_to(&rhs.span);
                lhs = self.mk_expr(ast::ExprKind::Labeled(Box::new(lhs), Box::new(rhs)), span);
                continue;
            }

            let rhs = self.parse_infix_expr(prec + prec_adjustment, None, &ctx)?;
            ctx.restrictions -= Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA;

            let span = lhs.span.extend_to(&rhs.span);

            if matches!(op, ast::InfixOp::Colon) && matches!(lhs.kind, ast::ExprKind::Name(_)) {
                lhs = self.mk_expr(ast::ExprKind::Labeled(Box::new(lhs), Box::new(rhs)), span);
                continue;
            }

            let kind = match op {
                ast::InfixOp::Assign | ast::InfixOp::AssignOp(_) => {
                    ast::ExprKind::Assign(ast::Assign {
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        is_mut: false,
                        mut_span: None,
                        op,
                        op_span,
                    })
                }
                ast::InfixOp::Comma => {
                    let mut items = if let ast::ExprKind::Sequence(lhs_seq) = lhs.kind {
                        lhs_seq.items
                    } else {
                        vec![lhs]
                    };

                    if let ast::ExprKind::Sequence(rhs_seq) = rhs.kind {
                        items.extend(rhs_seq.items);
                    } else {
                        items.push(rhs)
                    };

                    ast::ExprKind::Sequence(ast::Sequence {
                        items,
                        trailing: false,
                    })
                }
                _ => ast::ExprKind::BinOp(ast::BinOp {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    op,
                    op_span,
                }),
            };

            lhs = self.mk_expr(kind, span)
        }

        Ok(lhs)
    }

    pub(crate) fn parse_prefix_expr(&mut self, ctx: &ParseContext) -> ParseResult<ast::Expr> {
        if let Some((op, tok_count)) = self.peek_prefix_op()? {
            let (_, op_span) = self.lex.consume_count(tok_count);
            let expr = self.parse_prefix_expr(ctx)?;
            let span = op_span.extend_to(&expr.span);
            Ok(self.mk_expr(
                ast::ExprKind::UnaryOp(ast::UnaryOp {
                    expr: Box::new(expr),
                    op,
                    op_span,
                }),
                span,
            ))
        } else {
            self.parse_postfix_expr(ctx)
        }
    }

    pub(crate) fn parse_range_expr(
        &mut self,
        prec: usize,
        start: ast::Expr,
        op: ast::InfixOp,
        op_span: Span,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let end = self.parse_infix_expr(prec + 1, None, ctx)?;
        let span = start.span.extend_to(&end.span);
        let limits = match op {
            ast::InfixOp::RangeInclusive => ast::RangeLimits::Inclusive,
            ast::InfixOp::RangeExclusive => ast::RangeLimits::Exclusive,
            _ => unreachable!(),
        };

        Ok(self.mk_expr(
            ast::ExprKind::Range(ast::Range {
                start: Box::new(start),
                end: Box::new(end),
                op_span,
                limits,
            }),
            span,
        ))
    }

    pub(crate) fn parse_cast_expr(
        &mut self,
        lhs: ast::Expr,
        as_span: Span,
        ctx: &ParseContext,
    ) -> ParseResult<ast::Expr> {
        let ty = self.parse_ty()?;
        let span = lhs.span.extend_to(&ty.span.unwrap());
        Ok(self.mk_expr(
            ast::ExprKind::Cast(ast::Cast {
                lhs: Box::new(lhs),
                ty,
                as_span,
            }),
            span,
        ))
    }

    pub(crate) fn peek_infix_op(
        &mut self,
        ctx: &ParseContext,
    ) -> ParseResult<Option<(ast::InfixOp, usize)>> {
        if self.is_eol() && !ctx.restrictions.contains(Restrictions::IN_PAREN) {
            return Ok(None);
        }

        use TokenKind::*;
        Ok(Some(
            match (self.peek_kind(), self.peek_kind_at(1), self.peek_kind_at(2)) {
                (Asterisk, Asterisk, Equals) => {
                    (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Pow)), 3)
                }
                (Ampersand, Ampersand, Equals) => {
                    (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::And)), 3)
                }
                (Lt, Lt, Equals) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::ShiftLeft)), 3),
                (Gt, Gt, Equals) => (
                    ast::InfixOp::AssignOp(Box::new(ast::InfixOp::ShiftRight)),
                    3,
                ),
                (Pipe, Pipe, Equals) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Or)), 3),
                (Plus, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Add)), 2),
                (Minus, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Sub)), 2),
                (Slash, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Div)), 2),
                (Percent, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Mod)), 2),
                (Asterisk, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::Mul)), 2),
                (Ampersand, Equals, _) => {
                    (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::BitAnd)), 2)
                }
                (Pipe, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::BitOr)), 2),
                (Caret, Equals, _) => (ast::InfixOp::AssignOp(Box::new(ast::InfixOp::BitXor)), 2),
                (Equals, Equals, _) => (ast::InfixOp::Eq, 2),
                (Exclamation, Equals, _) => (ast::InfixOp::NotEq, 2),
                (Asterisk, Asterisk, _) => (ast::InfixOp::Pow, 2),
                (Ampersand, Ampersand, _) => (ast::InfixOp::And, 2),
                (Pipe, Pipe, _) => (ast::InfixOp::Or, 2),
                (Gt, Equals, _) => (ast::InfixOp::GtEq, 2),
                (Lt, Equals, _) => (ast::InfixOp::LtEq, 2),
                (Lt, Lt, _) => (ast::InfixOp::ShiftLeft, 2),
                (Gt, Gt, _) => (ast::InfixOp::ShiftRight, 2),
                (RangeExclusive, _, _) => (ast::InfixOp::RangeExclusive, 1),
                (RangeInclusive, _, _) => (ast::InfixOp::RangeInclusive, 1),
                (As, _, _) => (ast::InfixOp::As, 1),
                (Else, _, _) => (ast::InfixOp::Else, 1),
                (Comma, _, _) => (ast::InfixOp::Comma, 1),
                (Colon, _, _) => (ast::InfixOp::Colon, 1),
                (Lt, _, _) => (ast::InfixOp::Lt, 1),
                (Gt, _, _) => (ast::InfixOp::Gt, 1),
                (Plus, _, _) => (ast::InfixOp::Add, 1),
                (Minus, _, _) => (ast::InfixOp::Sub, 1),
                (Slash, _, _) => (ast::InfixOp::Div, 1),
                (Percent, _, _) => (ast::InfixOp::Mod, 1),
                (Asterisk, _, _) => (ast::InfixOp::Mul, 1),
                (Ampersand, _, _) => (ast::InfixOp::BitAnd, 1),
                (Pipe, _, _) => (ast::InfixOp::BitOr, 1),
                (Caret, _, _) => (ast::InfixOp::BitXor, 1),
                (Equals, _, _) => (ast::InfixOp::Assign, 1),
                _ => return Ok(None),
            },
        ))
    }

    pub(crate) fn peek_prefix_op(&mut self) -> ParseResult<Option<(ast::PrefixOp, usize)>> {
        use TokenKind::*;
        Ok(Some(match (self.peek_kind(), self.peek_kind_at(1)) {
            (Gt, Minus) => (ast::PrefixOp::Receive, 2),
            (Plus, _) => (ast::PrefixOp::Positive, 1),
            (Minus, _) => (ast::PrefixOp::Negative, 1),
            (Asterisk, _) => (ast::PrefixOp::Deref, 1),
            (Ampersand, _) => (ast::PrefixOp::Ref, 1),
            (Exclamation, _) => (ast::PrefixOp::Not, 1),
            (Tilde, _) => (ast::PrefixOp::BitNot, 1),
            _ => return Ok(None),
        }))
    }
}
