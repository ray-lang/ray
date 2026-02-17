use crate::{
    ast::{Export, ExportKind, Import, ImportKind, TrailingPolicy, token::TokenKind},
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
    ///   import a                    - namespace handle, access via `a::NAME`
    ///   import a::b                 - namespace handle, access via `b::NAME`
    ///   import a::b with C, D, E    - selective import, C, D, E directly accessible
    ///   import a::b with *          - glob import, all exports directly accessible
    ///   import "C" "stdlib.h"       - C header import
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
            // Recovery: if path parsing fails, produce an Incomplete import
            let path = match parser.parse_path(ctx) {
                Ok(p) => p,
                Err(err) => {
                    parser.record_parse_error(err);
                    let end = parser.lex.position();
                    return Ok(Import {
                        kind: ImportKind::Incomplete,
                        span: Span { start, end },
                    });
                }
            };
            let path_span = parser.srcmap.span_of(&path);
            let mut end = path_span.end;
            let kind = if peek!(parser, TokenKind::With) {
                let _with_span = parser.expect_keyword(TokenKind::With, ctx)?;

                // Check for glob import: `with *`
                if peek!(parser, TokenKind::Asterisk) {
                    let star_span = parser.expect_sp(TokenKind::Asterisk, ctx)?;
                    end = star_span.end;
                    ImportKind::Glob(path)
                } else {
                    // Selective import: `with name1, name2`
                    // Allow trailing commas for LSP completion after `import x with Add,`
                    let spec = SeqSpec {
                        delimiters: None,
                        trailing: TrailingPolicy::Allow,
                        newline: NewlineMode::Suppress,
                        restrictions: Restrictions::empty(),
                    };
                    // Recovery: if names parsing fails, produce Names with empty list
                    match parser.parse_delimited_seq(spec, ctx, |parser, trailing, _, ctx| {
                        parser.parse_sep_seq(
                            &TokenKind::Comma,
                            trailing,
                            None,
                            ctx,
                            |parser, ctx| parser.parse_name_with_type(None, ctx),
                        )
                    }) {
                        Ok(((names, _), spans)) => {
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
                            ImportKind::Names(path, names)
                        }
                        Err(err) => {
                            parser.record_parse_error(err);
                            end = parser.lex.position();
                            ImportKind::Names(path, vec![])
                        }
                    }
                }
            } else {
                ImportKind::Path(path)
            };

            Import {
                kind,
                span: Span { start, end },
            }
        })
    }

    /// Parses an export statement
    ///
    /// Examples:
    ///   export a                    - re-export module as namespace
    ///   export a::b                 - re-export module as namespace
    ///   export a::b with C, D, E    - selectively re-export specific names
    ///   export a::b with *          - re-export all exports from module
    pub(crate) fn parse_export(&mut self, ctx: &ParseContext) -> ParseResult<Export> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parse export statement");
        let ctx = &parser.ctx_clone();
        let export_span = parser.expect_keyword(TokenKind::Export, ctx)?;
        let start = export_span.start;

        // Recovery: if path parsing fails, produce an Incomplete export
        let path = match parser.parse_path(ctx) {
            Ok(p) => p,
            Err(err) => {
                parser.record_parse_error(err);
                let end = parser.lex.position();
                return Ok(Export {
                    kind: ExportKind::Incomplete,
                    span: Span { start, end },
                });
            }
        };
        let path_span = parser.srcmap.span_of(&path);
        let mut end = path_span.end;
        let kind = if peek!(parser, TokenKind::With) {
            let _with_span = parser.expect_keyword(TokenKind::With, ctx)?;

            // Check for glob export: `with *`
            if peek!(parser, TokenKind::Asterisk) {
                let star_span = parser.expect_sp(TokenKind::Asterisk, ctx)?;
                end = star_span.end;
                ExportKind::Glob(path)
            } else {
                // Selective export: `with name1, name2`
                // Allow trailing commas for LSP completion after `export x with Foo,`
                let spec = SeqSpec {
                    delimiters: None,
                    trailing: TrailingPolicy::Allow,
                    newline: NewlineMode::Suppress,
                    restrictions: Restrictions::empty(),
                };
                // Recovery: if names parsing fails, produce Names with empty list
                match parser.parse_delimited_seq(spec, ctx, |parser, trailing, _, ctx| {
                    parser.parse_sep_seq(&TokenKind::Comma, trailing, None, ctx, |parser, ctx| {
                        parser.parse_name_with_type(None, ctx)
                    })
                }) {
                    Ok(((names, _), spans)) => {
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
                        ExportKind::Names(path, names)
                    }
                    Err(err) => {
                        parser.record_parse_error(err);
                        end = parser.lex.position();
                        ExportKind::Names(path, vec![])
                    }
                }
            }
        } else {
            ExportKind::Path(path)
        };

        Ok(Export {
            kind,
            span: Span { start, end },
        })
    }
}
