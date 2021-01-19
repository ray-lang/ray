use crate::{
    ast::{token::TokenKind, Import, Path, Trailing},
    parse::{ParseContext, ParseResult, Parser},
    span::Span,
};

impl Parser {
    /// Parses an import statement
    ///
    /// Examples:
    ///   import a
    ///   import a::b
    ///   import a::b with C, D, E
    ///   import "C" "stdlib.h"
    pub(crate) fn parse_import(&mut self, ctx: &ParseContext) -> ParseResult<Import> {
        let start = self.expect_start(TokenKind::Import)?;
        Ok(if must_peek!(self, TokenKind::DoubleQuote { .. }) {
            // "C"
            let (s, sp) = self.expect_string()?;
            if &s != "C" {
                return Err(
                    self.parse_error(format!("Expected string \"C\" but found \"{}\"", s), sp)
                );
            }

            let (c_import, sp) = self.expect_string()?;
            let end = sp.end;
            Import {
                path: Path::new(),
                with: None,
                span: Span { start, end },
                c_import: Some((c_import, sp)),
            }
        } else {
            let path = self.parse_path()?;
            let mut end = path.span.end;
            let with = if expect_if!(self, TokenKind::With) {
                let (names, span) = self.parse_name_seq(Trailing::Disallow, ctx)?;
                end = span.end;
                Some(names)
            } else {
                None
            };

            Import {
                path,
                with,
                span: Span { start, end },
                c_import: None,
            }
        })
    }
}
