use super::{DEPTH_IDX_BRACKET, DEPTH_IDX_CURLY, DEPTH_IDX_PAREN, ParseResult};
use super::{ExprResult, Parser, context::ParseContext};

use crate::ast::{Dict, Expr, List, Set, TrailingPolicy, ValueKind, token::TokenKind};
use crate::parse::{
    lexer::NewlineMode,
    parser::{Restrictions, context::SeqSpec},
};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CurlyBracedExprKind {
    Block,
    Dict,
    Set,
}

impl Parser<'_> {
    pub(crate) fn parse_array_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftBracket, TokenKind::RightBracket)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let (seq, spans) = self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
            parser.parse_expr_seq(ValueKind::RValue, trailing, stop, ctx)
        })?;

        let (l_span, r_span) = spans.expect("array expression must have bracket spans");
        let span = l_span.extend_to(&r_span);
        Ok(self.mk_expr(
            Expr::List(List {
                items: seq.items,
                lbrack_span: l_span,
                rbrack_span: r_span,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    pub(crate) fn parse_curly_braced_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        match self.peek_curly_braced_expr_kind()? {
            CurlyBracedExprKind::Block => self.parse_block(ctx),
            CurlyBracedExprKind::Dict => self.parse_dict_literal_expr(ctx),
            CurlyBracedExprKind::Set => self.parse_set_literal_expr(ctx),
        }
    }

    fn peek_curly_braced_expr_kind(&mut self) -> ParseResult<CurlyBracedExprKind> {
        use TokenKind::*;

        debug_assert!(matches!(self.peek_kind(), LeftCurly));

        match (self.peek_kind_at(1), self.peek_kind_at(2)) {
            (RightCurly, _) => return Ok(CurlyBracedExprKind::Dict),
            (Comma, RightCurly) => return Ok(CurlyBracedExprKind::Set),
            _ => {}
        }

        let mut depth = [0usize; 3];
        let mut idx = 1usize;
        let mut saw_top_level_comma = false;

        while !matches!(self.peek_kind_at(idx), EOF) {
            let kind = self.peek_kind_at(idx);
            let at_top_level = depth[DEPTH_IDX_PAREN] == 0
                && depth[DEPTH_IDX_BRACKET] == 0
                && depth[DEPTH_IDX_CURLY] == 0;

            match kind {
                LeftParen => depth[DEPTH_IDX_PAREN] += 1,
                RightParen => depth[DEPTH_IDX_PAREN] = depth[DEPTH_IDX_PAREN].saturating_sub(1),
                LeftBracket => depth[DEPTH_IDX_BRACKET] += 1,
                RightBracket => {
                    depth[DEPTH_IDX_BRACKET] = depth[DEPTH_IDX_BRACKET].saturating_sub(1)
                }
                LeftCurly => depth[DEPTH_IDX_CURLY] += 1,
                RightCurly => {
                    if depth[DEPTH_IDX_CURLY] == 0 {
                        break;
                    }
                    depth[DEPTH_IDX_CURLY] -= 1;
                }
                Colon if at_top_level => return Ok(CurlyBracedExprKind::Dict),
                Comma if at_top_level => saw_top_level_comma = true,
                _ => {}
            }

            idx += 1;
        }

        if saw_top_level_comma {
            Ok(CurlyBracedExprKind::Set)
        } else {
            Ok(CurlyBracedExprKind::Block)
        }
    }

    fn parse_dict_literal_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftCurly, TokenKind::RightCurly)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let ((entries, trailing_comma), spans) =
            self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                parser.parse_sep_seq(
                    &TokenKind::Comma,
                    trailing,
                    stop.as_ref(),
                    ctx,
                    |parser, ctx| {
                        let mut key_ctx = ctx.clone();
                        key_ctx.stop_token = Some(TokenKind::Colon);
                        let key = parser.parse_expr(&key_ctx)?;

                        parser.expect_sp(TokenKind::Colon, ctx)?;

                        let mut value_ctx = ctx.clone();
                        value_ctx.stop_token = Some(TokenKind::Comma);
                        let value = parser.parse_expr(&value_ctx)?;

                        Ok((key, value))
                    },
                )
            })?;

        let (l_span, r_span) = spans.expect("dict literal expression must have brace spans");
        let span = l_span.extend_to(&r_span);
        Ok(self.mk_expr(
            Expr::Dict(Dict {
                entries,
                lcurly_span: l_span,
                rcurly_span: r_span,
                trailing_comma,
            }),
            span,
            ctx.path.clone(),
        ))
    }

    fn parse_set_literal_expr(&mut self, ctx: &ParseContext) -> ExprResult {
        let spec = SeqSpec {
            delimiters: Some((TokenKind::LeftCurly, TokenKind::RightCurly)),
            trailing: TrailingPolicy::Allow,
            newline: NewlineMode::Suppress,
            restrictions: Restrictions::IN_PAREN,
        };

        let (items, spans) =
            self.parse_delimited_seq(spec, ctx, |parser, trailing, stop, ctx| {
                if matches!(parser.peek_kind(), TokenKind::Comma) {
                    parser.expect_sp(TokenKind::Comma, ctx)?;
                    return Ok((Vec::new(), true));
                }

                parser
                    .parse_expr_seq(ValueKind::RValue, trailing, stop, ctx)
                    .map(|seq| (seq.items, seq.trailing))
            })?;

        let (l_span, r_span) = spans.expect("set literal expression must have brace spans");
        let span = l_span.extend_to(&r_span);
        Ok(self.mk_expr(
            Expr::Set(Set {
                items: items.0,
                lcurly_span: l_span,
                rcurly_span: r_span,
                trailing_comma: items.1,
            }),
            span,
            ctx.path.clone(),
        ))
    }
}
