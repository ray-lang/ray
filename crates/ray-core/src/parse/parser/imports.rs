use crate::{
    ast::{Import, ImportKind, TrailingPolicy, token::TokenKind},
    parse::{
        ParseContext, ParseResult, Parser,
        lexer::NewlineMode,
        parser::{Restrictions, context::SeqSpec},
    },
};
use ray_shared::span::Span;

impl Parser<'_> {
    /// Parses an import statement
    ///
    /// Examples:
    ///   import a
    ///   import a::b
    ///   import a::b with C, D, E
    ///   import "C" "stdlib.h"
    pub(crate) fn parse_import(&mut self, ctx: &ParseContext) -> ParseResult<Import> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse import statement");
        let ctx = &parser.ctx_clone();
        let import_span = parser.expect_keyword(TokenKind::Import, ctx)?;
        let start = import_span.start;
        Ok(if must_peek!(parser, TokenKind::DoubleQuote { .. }) {
            // "C"
            let (s, sp) = parser.expect_string(ctx)?;
            if &s != "C" {
                return Err(parser.parse_error(
                    format!("Expected string \"C\" but found \"{}\"", s),
                    sp,
                    ctx,
                ));
            }

            let (header_path, sp) = parser.expect_string(ctx)?;
            let end = sp.end;
            Import {
                kind: ImportKind::CImport(header_path, sp),
                span: Span { start, end },
            }
        } else {
            let path = parser.parse_path(ctx)?;
            let path_span = parser.srcmap.span_of(&path);
            let mut end = path_span.end;
            let with = if peek!(parser, TokenKind::With) {
                let _with_span = parser.expect_keyword(TokenKind::With, ctx)?;
                let spec = SeqSpec {
                    delimiters: None,
                    trailing: TrailingPolicy::Forbid,
                    newline: NewlineMode::Suppress,
                    restrictions: Restrictions::empty(),
                };
                let ((names, _), spans) =
                    parser.parse_delimited_seq(spec, ctx, |parser, trailing, _, ctx| {
                        parser.parse_sep_seq(
                            &TokenKind::Comma,
                            trailing,
                            None,
                            ctx,
                            |parser, ctx| parser.parse_name_with_type(None, ctx),
                        )
                    })?;

                let span = if let Some((left, right)) = spans {
                    Span {
                        start: left.start,
                        end: right.end,
                    }
                } else if let Some(first) = names.first()
                    && let Some(last) = names.last()
                {
                    let first_span = parser.srcmap.span_of(first);
                    let last_span = parser.srcmap.span_of(last);
                    Span {
                        start: first_span.start,
                        end: last_span.end,
                    }
                } else {
                    Span {
                        start: path_span.end,
                        end: path_span.end,
                    }
                };

                let names = names.into_iter().map(|n| n.take_map(|n| n.path)).collect();
                end = span.end;
                Some(names)
            } else {
                None
            };

            let kind = if let Some(with) = with {
                ImportKind::Names(path, with)
            } else {
                ImportKind::Path(path)
            };

            Import {
                kind,
                span: Span { start, end },
            }
        })
    }
}
