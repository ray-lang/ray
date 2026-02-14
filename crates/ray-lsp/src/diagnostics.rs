//! Diagnostic conversion helpers for the LSP server.
//!
//! Converts `RayError` values (from the incremental query system) into
//! LSP `Diagnostic` values suitable for `textDocument/publishDiagnostics`.

use std::collections::HashSet;

use ray_core::errors::RayError;
use ray_shared::{
    pathlib::FilePath,
    span::{Pos, Source, Span},
};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range};

/// Convert a list of `RayError`s into LSP `Diagnostic`s, filtering to the given file.
///
/// Only source locations whose filepath matches `target` are included.
pub(crate) fn map_errors(errors: Vec<RayError>, target: &FilePath) -> Vec<Diagnostic> {
    errors
        .into_iter()
        .flat_map(|error| map_error(error, target))
        .collect()
}

/// Deduplicate diagnostics by message + start position + severity + source.
///
/// Ignores end position to collapse double-EOF variants.
pub(crate) fn dedup_diagnostics(mut diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut seen = HashSet::new();
    diags.retain(|d| {
        let sev_dbg = d.severity.as_ref().map(|s| format!("{:?}", s));
        let key = (
            d.message.clone(),
            d.range.start.line,
            d.range.start.character,
            sev_dbg,
            d.source.clone(),
        );
        seen.insert(key)
    });
    diags
}

fn map_error(error: RayError, target: &FilePath) -> Vec<Diagnostic> {
    let RayError { msg, src, .. } = error;
    src.into_iter()
        .filter_map(|mut source| {
            if source.filepath.is_empty() {
                source.filepath = target.clone();
            }

            if source.filepath != *target {
                None
            } else {
                Some(make_diagnostic(&msg, &source))
            }
        })
        .collect()
}

fn make_diagnostic(message: &str, source: &Source) -> Diagnostic {
    let range = source.span.map(span_to_range).unwrap_or_else(default_range);

    Diagnostic {
        range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: None,
        code_description: None,
        source: Some("ray".to_string()),
        message: message.to_string(),
        related_information: None,
        tags: None,
        data: None,
    }
}

fn span_to_range(span: Span) -> Range {
    let mut start = pos_to_position(span.start);
    let mut end = pos_to_position(span.end);
    if (end.line, end.character) < (start.line, start.character) {
        std::mem::swap(&mut start, &mut end);
    }
    Range::new(start, end)
}

fn pos_to_position(pos: Pos) -> Position {
    Position::new(pos.lineno as u32, pos.col as u32)
}

fn default_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 0))
}
