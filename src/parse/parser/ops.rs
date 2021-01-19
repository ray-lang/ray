use super::{ExprResult, ParseContext, ParseResult, ParsedExpr, Parser, Restrictions};

use crate::{
    ast::{
        token::TokenKind, Assign, Associativity, BinOp, Cast, Expr, InfixOp, PrefixOp, Range,
        RangeLimits, Sequence, UnaryOp,
    },
    span::Span,
};

impl Parser {
    pub(crate) fn parse_infix_expr(
        &mut self,
        min_prec: usize,
        lhs: Option<ParsedExpr>,
        ctx: &ParseContext,
    ) -> ExprResult {
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

            if op == InfixOp::Else && ctx.restrictions.contains(Restrictions::IF_ELSE) {
                // handle the if .. else case
                // TODO: is there a case of `if .. else .. else`?
                break;
            }

            let (_, op_span) = self.lex.consume_count(tok_count);

            match (self.peek_kind(), &ctx.stop_token) {
                (k, Some(t)) if &k == t => {
                    if matches!(op, InfixOp::Comma) {
                        if let Expr::Sequence(seq) = &mut lhs.value {
                            seq.trailing = true;
                        } else {
                            let span = lhs.info.src.span.unwrap().extend_to(&op_span);
                            lhs = self.mk_expr(
                                Expr::Sequence(Sequence {
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

            if op == InfixOp::RangeInclusive || op == InfixOp::RangeExclusive {
                lhs = self.parse_range_expr(prec, lhs, op, op_span, &ctx)?;
                break;
            }

            if op == InfixOp::As {
                lhs = self.parse_cast_expr(lhs, op_span, &ctx)?;
                continue;
            }

            let associativity = op.associativity();
            let prec_adjustment = match associativity {
                Associativity::Right => 0,
                Associativity::Left | Associativity::None => 1,
            };

            if matches!(op, InfixOp::Assign | InfixOp::AssignOp(_)) {
                ctx.restrictions |= Restrictions::ASSIGN;
                ctx.restrictions -= Restrictions::LVALUE;
            }

            if matches!(op, InfixOp::Comma) {
                ctx = ctx.clone();
                ctx.restrictions |= Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA;
            } else if matches!(op, InfixOp::Colon) && !matches!(lhs.value, Expr::Name(_)) {
                // this is a typed expression
                let ty = self.parse_ty()?;
                let ty_span = ty.span.unwrap();
                let rhs = self.mk_expr(Expr::Type(ty), ty_span);
                let span = lhs
                    .info
                    .src
                    .span
                    .unwrap()
                    .extend_to(&rhs.info.src.span.unwrap());
                lhs = self.mk_expr(Expr::Labeled(Box::new(lhs), Box::new(rhs)), span);
                continue;
            }

            let rhs = self.parse_infix_expr(prec + prec_adjustment, None, &ctx)?;
            ctx.restrictions -= Restrictions::EXPECT_EXPR | Restrictions::AFTER_COMMA;

            let span = lhs
                .info
                .src
                .span
                .unwrap()
                .extend_to(&rhs.info.src.span.unwrap());

            if matches!(op, InfixOp::Colon) && matches!(lhs.value, Expr::Name(_)) {
                lhs = self.mk_expr(Expr::Labeled(Box::new(lhs), Box::new(rhs)), span);
                continue;
            }

            let kind = match op {
                InfixOp::Assign | InfixOp::AssignOp(_) => Expr::Assign(Assign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    is_mut: false,
                    mut_span: None,
                    op,
                    op_span,
                }),
                InfixOp::Comma => {
                    let mut items = if let Expr::Sequence(lhs_seq) = lhs.value {
                        lhs_seq.items
                    } else {
                        vec![lhs]
                    };

                    if let Expr::Sequence(rhs_seq) = rhs.value {
                        items.extend(rhs_seq.items);
                    } else {
                        items.push(rhs)
                    };

                    Expr::Sequence(Sequence {
                        items,
                        trailing: false,
                    })
                }
                _ => Expr::BinOp(BinOp {
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

    pub(crate) fn parse_prefix_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        if let Some((op, tok_count)) = self.peek_prefix_op()? {
            let (_, op_span) = self.lex.consume_count(tok_count);
            let expr = self.parse_prefix_expr(ctx)?;
            let span = op_span.extend_to(&expr.info.src.span.unwrap());
            Ok(self.mk_expr(
                Expr::UnaryOp(UnaryOp {
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
        start: ParsedExpr,
        op: InfixOp,
        op_span: Span,
        ctx: &ParseContext,
    ) -> ExprResult {
        let end = self.parse_infix_expr(prec + 1, None, ctx)?;
        let span = start
            .info
            .src
            .span
            .unwrap()
            .extend_to(&end.info.src.span.unwrap());
        let limits = match op {
            InfixOp::RangeInclusive => RangeLimits::Inclusive,
            InfixOp::RangeExclusive => RangeLimits::Exclusive,
            _ => unreachable!(),
        };

        Ok(self.mk_expr(
            Expr::Range(Range {
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
        lhs: ParsedExpr,
        as_span: Span,
        ctx: &ParseContext,
    ) -> ExprResult {
        let ty = self.parse_ty()?;
        let span = lhs.info.src.span.unwrap().extend_to(&ty.span.unwrap());
        Ok(self.mk_expr(
            Expr::Cast(Cast {
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
    ) -> ParseResult<Option<(InfixOp, usize)>> {
        if self.is_eol() && !ctx.restrictions.contains(Restrictions::IN_PAREN) {
            return Ok(None);
        }

        use TokenKind::*;
        Ok(Some(
            match (self.peek_kind(), self.peek_kind_at(1), self.peek_kind_at(2)) {
                (Asterisk, Asterisk, Equals) => (InfixOp::AssignOp(Box::new(InfixOp::Pow)), 3),
                (Ampersand, Ampersand, Equals) => (InfixOp::AssignOp(Box::new(InfixOp::And)), 3),
                (Lt, Lt, Equals) => (InfixOp::AssignOp(Box::new(InfixOp::ShiftLeft)), 3),
                (Gt, Gt, Equals) => (InfixOp::AssignOp(Box::new(InfixOp::ShiftRight)), 3),
                (Pipe, Pipe, Equals) => (InfixOp::AssignOp(Box::new(InfixOp::Or)), 3),
                (Plus, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::Add)), 2),
                (Minus, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::Sub)), 2),
                (Slash, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::Div)), 2),
                (Percent, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::Mod)), 2),
                (Asterisk, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::Mul)), 2),
                (Ampersand, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::BitAnd)), 2),
                (Pipe, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::BitOr)), 2),
                (Caret, Equals, _) => (InfixOp::AssignOp(Box::new(InfixOp::BitXor)), 2),
                (Equals, Equals, _) => (InfixOp::Eq, 2),
                (Exclamation, Equals, _) => (InfixOp::NotEq, 2),
                (Asterisk, Asterisk, _) => (InfixOp::Pow, 2),
                (Ampersand, Ampersand, _) => (InfixOp::And, 2),
                (Pipe, Pipe, _) => (InfixOp::Or, 2),
                (Gt, Equals, _) => (InfixOp::GtEq, 2),
                (Lt, Equals, _) => (InfixOp::LtEq, 2),
                (Lt, Lt, _) => (InfixOp::ShiftLeft, 2),
                (Gt, Gt, _) => (InfixOp::ShiftRight, 2),
                (RangeExclusive, _, _) => (InfixOp::RangeExclusive, 1),
                (RangeInclusive, _, _) => (InfixOp::RangeInclusive, 1),
                (As, _, _) => (InfixOp::As, 1),
                (Else, _, _) => (InfixOp::Else, 1),
                (Comma, _, _) => (InfixOp::Comma, 1),
                (Colon, _, _) => (InfixOp::Colon, 1),
                (Lt, _, _) => (InfixOp::Lt, 1),
                (Gt, _, _) => (InfixOp::Gt, 1),
                (Plus, _, _) => (InfixOp::Add, 1),
                (Minus, _, _) => (InfixOp::Sub, 1),
                (Slash, _, _) => (InfixOp::Div, 1),
                (Percent, _, _) => (InfixOp::Mod, 1),
                (Asterisk, _, _) => (InfixOp::Mul, 1),
                (Ampersand, _, _) => (InfixOp::BitAnd, 1),
                (Pipe, _, _) => (InfixOp::BitOr, 1),
                (Caret, _, _) => (InfixOp::BitXor, 1),
                (Equals, _, _) => (InfixOp::Assign, 1),
                _ => return Ok(None),
            },
        ))
    }

    pub(crate) fn peek_prefix_op(&mut self) -> ParseResult<Option<(PrefixOp, usize)>> {
        use TokenKind::*;
        Ok(Some(match (self.peek_kind(), self.peek_kind_at(1)) {
            (Gt, Minus) => (PrefixOp::Receive, 2),
            (Plus, _) => (PrefixOp::Positive, 1),
            (Minus, _) => (PrefixOp::Negative, 1),
            (Asterisk, _) => (PrefixOp::Deref, 1),
            (Ampersand, _) => (PrefixOp::Ref, 1),
            (Exclamation, _) => (PrefixOp::Not, 1),
            (Tilde, _) => (PrefixOp::BitNot, 1),
            _ => return Ok(None),
        }))
    }
}
