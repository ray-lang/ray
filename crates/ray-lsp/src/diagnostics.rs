use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use ray_core::{
    ast::{Decl, Module, Path},
    errors::RayError,
    libgen::DefinitionRecord,
    parse::{ParseOptions, Parser},
    sema::{NameContext, SymbolMap},
    span::{Source, SourceMap},
};
use ray_core::{
    pathlib::{FilePath, RayPaths},
    span,
};
use ray_driver::{BuildOptions, Driver, FrontendResult};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range, Url};

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AnalysisSnapshotData {
    pub module_path: Path,
    pub entry_path: FilePath,
    pub module: Module<(), Decl>,
    pub name_context: NameContext,
    pub srcmap: SourceMap,
    pub symbol_map: SymbolMap,
    pub definitions: HashMap<Path, DefinitionRecord>,
    pub module_paths: HashSet<Path>,
}

pub enum CollectResult {
    Diagnostics {
        diagnostics: Vec<Diagnostic>,
        snapshot: Option<AnalysisSnapshotData>,
    },
    ToolchainMissing,
}

fn is_core_library_uri(uri: &Url) -> bool {
    use std::path::Component;
    if let Ok(path) = uri.to_file_path() {
        // Match .../lib/core/... in a platform-independent way.
        let mut seen_lib = false;
        for comp in path.components() {
            match comp {
                Component::Normal(os) if os == "lib" => seen_lib = true,
                Component::Normal(os) if seen_lib && os == "core" => return true,
                _ => {}
            }
        }
    }
    false
}

pub fn collect(
    uri: &Url,
    text: &str,
    workspace_root: Option<&FilePath>,
    toolchain_root: Option<&FilePath>,
) -> CollectResult {
    let filepath = to_filepath(uri);
    // When editing core sources, instruct the analyzer to run with "no core" (don't load prebuilt core),
    // so diagnostics reflect the live core files in the workspace.
    let no_core: bool = is_core_library_uri(uri);
    let mut options = ParseOptions::default();
    options.module_path = Path::new();
    options.use_stdin = false;
    options.filepath = filepath.clone();
    options.original_filepath = filepath.clone();

    let mut srcmap = SourceMap::new();
    let parsed = Parser::parse_from_src_with_diagnostics(text, options, &mut srcmap);

    let mut diagnostics: Vec<Diagnostic> = parsed
        .errors
        .into_iter()
        .flat_map(|error| map_error(error, &filepath))
        .collect();

    if !diagnostics.is_empty() {
        return CollectResult::Diagnostics {
            diagnostics: dedup_diagnostics(diagnostics),
            snapshot: None,
        };
    }

    match collect_semantic_errors(text, &filepath, workspace_root, toolchain_root, no_core) {
        Ok((semantic_errors, snapshot)) => {
            diagnostics.extend(
                semantic_errors
                    .into_iter()
                    .flat_map(|error| map_error(error, &filepath)),
            );
            CollectResult::Diagnostics {
                diagnostics: dedup_diagnostics(diagnostics),
                snapshot,
            }
        }
        Err(SemanticError::ToolchainMissing) => CollectResult::ToolchainMissing,
    }
}

enum SemanticError {
    ToolchainMissing,
}

fn collect_semantic_errors(
    text: &str,
    filepath: &FilePath,
    workspace_root: Option<&FilePath>,
    toolchain_root: Option<&FilePath>,
    no_core: bool,
) -> Result<(Vec<RayError>, Option<AnalysisSnapshotData>), SemanticError> {
    let ray_paths = match RayPaths::discover(toolchain_root.cloned(), workspace_root) {
        Some(paths) => paths,
        None => return Err(SemanticError::ToolchainMissing),
    };

    let mut overlays = HashMap::new();
    overlays.insert(filepath.clone(), text.to_string());

    // let entry_path = root::module_entry_path(filepath);
    let build_options = BuildOptions {
        // input_path: entry_path.clone(),
        input_path: filepath.clone(),
        no_core,
        ..Default::default()
    };
    let driver = Driver::new(ray_paths);
    let result = match driver.build_frontend(&build_options, Some(overlays)) {
        Ok(result) => result,
        Err(errors) => return Ok((errors, None)),
    };

    let FrontendResult {
        module_path,
        module,
        tcx: _,
        ncx,
        srcmap,
        symbol_map,
        defs: _,
        libs: _,
        paths,
        definitions,
    } = result;

    let snapshot = AnalysisSnapshotData {
        module_path,
        entry_path: filepath.clone(),
        module,
        name_context: ncx,
        srcmap,
        symbol_map,
        definitions,
        module_paths: paths,
    };

    Ok((vec![], Some(snapshot)))
}

fn dedup_diagnostics(mut diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
    use std::collections::HashSet;
    let mut seen = HashSet::new();
    diags.retain(|d| {
        // Dedup by message + start position (+ severity/source). Ignore end pos to collapse double-EOF variants.
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
    let diagnostics: Vec<Diagnostic> = src
        .into_iter()
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
        .collect();

    // if diagnostics.is_empty() {
    //     diagnostics.push(Diagnostic {
    //         range: default_range(),
    //         severity: Some(DiagnosticSeverity::ERROR),
    //         code: None,
    //         code_description: None,
    //         source: Some("ray".to_string()),
    //         message: msg,
    //         related_information: None,
    //         tags: None,
    //         data: None,
    //     });
    // }

    diagnostics
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

fn span_to_range(span: span::Span) -> Range {
    let mut start = pos_to_position(span.start);
    let mut end = pos_to_position(span.end);
    if (end.line, end.character) < (start.line, start.character) {
        std::mem::swap(&mut start, &mut end);
    }
    Range::new(start, end)
}

fn pos_to_position(pos: span::Pos) -> Position {
    Position::new(pos.lineno as u32, pos.col as u32)
}

fn default_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 0))
}

fn to_filepath(uri: &Url) -> FilePath {
    if let Ok(path) = uri.to_file_path() {
        FilePath::from(path)
    } else {
        FilePath::from(PathBuf::from(uri.path()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    fn expect_diagnostics(result: CollectResult) -> Vec<Diagnostic> {
        match result {
            CollectResult::Diagnostics { diagnostics, .. } => diagnostics,
            CollectResult::ToolchainMissing => {
                panic!("expected diagnostics, but toolchain was reported missing")
            }
        }
    }

    fn test_uri() -> Url {
        Url::parse("file:///diagnostics_test.ray").expect("valid file uri")
    }

    fn workspace_root() -> FilePath {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace_root = manifest_dir
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root is available");
        FilePath::from(workspace_root.to_path_buf())
    }

    #[test]
    fn returns_no_diagnostics_for_valid_source() {
        fern::Dispatch::new()
            .level(log::LevelFilter::Debug)
            .chain(std::io::stderr())
            .apply()
            .unwrap();
        let uri = test_uri();
        let root = workspace_root();
        let diagnostics = expect_diagnostics(collect(
            &uri,
            "fn main() {\n    mut x = 1\n}\n",
            Some(&root),
            Some(&root),
        ));
        assert!(
            diagnostics.is_empty(),
            "expected no diagnostics, got {diagnostics:?}"
        );
    }

    #[test]
    fn reports_parse_error_for_invalid_source() {
        let uri = test_uri();
        let root = workspace_root();
        let diagnostics =
            expect_diagnostics(collect(&uri, "fn main() {\n", Some(&root), Some(&root)));
        assert!(
            !diagnostics.is_empty(),
            "expected diagnostics for parse error"
        );

        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.severity, Some(DiagnosticSeverity::ERROR));
        assert_eq!(diagnostic.source.as_deref(), Some("ray"));
        assert!(
            !diagnostic.message.trim().is_empty(),
            "diagnostic message should not be empty"
        );
        assert!(
            diagnostic.range.start.line <= diagnostic.range.end.line,
            "range should have a non-decreasing line ordering"
        );
    }

    #[test]
    fn reports_name_error_from_analyzer() {
        let uri = test_uri();
        let root = workspace_root();
        let diagnostics = expect_diagnostics(collect(
            &uri,
            "fn main() {\n    does_not_exist()\n}\n",
            Some(&root),
            Some(&root),
        ));

        assert!(
            diagnostics
                .iter()
                .any(|diag| diag.message.contains("does_not_exist")),
            "expected an analyzer diagnostic about `does_not_exist`, got {diagnostics:?}"
        );
    }
}
