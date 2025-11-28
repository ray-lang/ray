use std::path::PathBuf;

use tower_lsp::lsp_types::{Position, Range, Url};

use ray_shared::pathlib::FilePath;
use ray_shared::span::Span;
use serde_json::Value;

pub(crate) fn parse_toolchain_path(value: &Value) -> Option<FilePath> {
    match value {
        Value::Null => None,
        Value::String(s) => to_filepath(s),
        Value::Object(map) => map
            .get("toolchainPath")
            .and_then(Value::as_str)
            .and_then(to_filepath)
            .or_else(|| {
                map.get("toolchain_path")
                    .and_then(Value::as_str)
                    .and_then(to_filepath)
            }),
        _ => None,
    }
}

pub(crate) fn to_filepath(s: &str) -> Option<FilePath> {
    if s.trim().is_empty() {
        None
    } else {
        Some(FilePath::from(PathBuf::from(s)))
    }
}

pub(crate) fn uri_to_filepath(uri: &Url) -> Option<FilePath> {
    if let Ok(path) = uri.to_file_path() {
        Some(FilePath::from(path))
    } else {
        to_filepath(uri.path())
    }
}

pub(crate) fn span_to_range(mut span: Span) -> Range {
    if (span.end.lineno, span.end.col) < (span.start.lineno, span.start.col) {
        std::mem::swap(&mut span.start, &mut span.end);
    }
    let start = Position::new(span.start.lineno as u32, span.start.col as u32);
    let end = Position::new(span.end.lineno as u32, span.end.col as u32);
    Range::new(start, end)
}

pub(crate) fn filepath_to_uri(filepath: &FilePath) -> Option<Url> {
    Url::from_file_path(filepath.as_ref()).ok()
}
