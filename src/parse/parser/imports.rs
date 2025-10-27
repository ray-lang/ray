use crate::{
    ast::{Import, ImportKind, Trailing, token::TokenKind},
    parse::{ParseContext, ParseResult, Parser},
    span::Span,
};

impl Parser<'_> {
    /// Parses an import statement
    ///
    /// Examples:
    ///   import a
    ///   import a::b
    ///   import a::b with C, D, E
    ///   import "C" "stdlib.h"
    pub(crate) fn parse_import(&mut self, ctx: &ParseContext) -> ParseResult<Import> {
        ctx.with_description("parse import statement", |ctx| {
            let import_span = self.expect_keyword(TokenKind::Import, ctx)?;
            let start = import_span.start;
            Ok(if must_peek!(self, TokenKind::DoubleQuote { .. }) {
                // "C"
                let (s, sp) = self.expect_string(ctx)?;
                if &s != "C" {
                    return Err(self.parse_error(
                        format!("Expected string \"C\" but found \"{}\"", s),
                        sp,
                        ctx,
                    ));
                }

                let (header_path, sp) = self.expect_string(ctx)?;
                let end = sp.end;
                Import {
                    kind: ImportKind::CImport(header_path, sp),
                    span: Span { start, end },
                }
            } else {
                let path = self.parse_path(ctx)?;
                let mut end = self.srcmap.span_of(&path).end;
                let with = if peek!(self, TokenKind::With) {
                    let _with_span = self.expect_keyword(TokenKind::With, ctx)?;
                    let (names, span) = self.parse_name_seq(Trailing::Disallow, None, ctx)?;
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
        })
    }
}
