use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use ray_codegen::libgen::DefinitionRecord;
use ray_core::{
    ast::{Decl, Module},
    errors::RayError,
    parse::{ParseOptions, Parser},
    sema::SymbolMap,
    sourcemap::SourceMap,
};
use ray_driver::{BuildOptions, Driver, FrontendResult};
use ray_shared::{
    collections::namecontext::NameContext,
    file_id::FileId,
    pathlib::{FilePath, Path, RayPaths},
};
use ray_shared::{
    node_id::NodeId,
    span::{Pos, Source, Span},
};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range, Url};

use crate::helpers::{is_core_library_uri, uri_to_filepath};

#[derive(Debug, Clone)]
pub struct TypeInfoSnapshot {
    pub ty: String,
    #[allow(dead_code)]
    pub is_scheme: bool,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AnalysisSnapshotData {
    pub module_path: Path,
    pub entry_path: FilePath,
    pub name_context: NameContext,
    pub srcmap: SourceMap,
    pub node_type_info: HashMap<NodeId, TypeInfoSnapshot>,
    pub symbol_map: SymbolMap,
    pub definitions: HashMap<Path, DefinitionRecord>,
    pub definitions_by_id: HashMap<NodeId, DefinitionRecord>,
    pub module_paths: HashSet<Path>,
}

pub enum CollectResult {
    Diagnostics {
        diagnostics: Vec<Diagnostic>,
        snapshot: Option<AnalysisSnapshotData>,
    },
    ToolchainMissing,
}

#[derive(Debug, Clone)]
pub struct CollectOptions {
    pub force_no_core: bool,
    pub workspace_root: Option<FilePath>,
    pub toolchain_root: Option<FilePath>,
}

pub fn collect(
    uri: &Url,
    text: &str,
    workspace_root: Option<&FilePath>,
    toolchain_root: Option<&FilePath>,
) -> CollectResult {
    collect_with_options(
        uri,
        text,
        CollectOptions {
            force_no_core: false,
            workspace_root: workspace_root.cloned(),
            toolchain_root: toolchain_root.cloned(),
        },
    )
}

pub fn collect_with_options(uri: &Url, text: &str, options: CollectOptions) -> CollectResult {
    let filepath =
        uri_to_filepath(uri).unwrap_or_else(|| FilePath::from(PathBuf::from(uri.path())));
    log::info!("collecting filepath: {}", filepath);

    // When editing core sources, instruct the analyzer to run with "no core" (don't load prebuilt core),
    // so diagnostics reflect the live core files in the workspace.
    let mut no_core: bool = options.force_no_core || is_core_library_uri(uri);
    let mut parse_options = ParseOptions::default();
    parse_options.module_path = Path::new();
    parse_options.use_stdin = false;
    parse_options.filepath = filepath.clone();
    parse_options.original_filepath = filepath.clone();

    let mut srcmap = SourceMap::new();
    let parsed =
        Parser::parse_from_src_with_diagnostics(FileId(0), text, parse_options, &mut srcmap);

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

    if let Some(file) = parsed.value
        && !no_core
    {
        // check the document comment for `[no-core]`
        if let Some(doc_comment) = &file.doc_comment {
            no_core = doc_comment.contains("[no-core]");
            log::info!("no_core={}, doc_comment={}", no_core, doc_comment);
        } else {
            log::info!("doc comment is missing");
        }
    }

    match collect_semantic_errors(
        text,
        &filepath,
        options.workspace_root.as_ref(),
        options.toolchain_root.as_ref(),
        no_core,
    ) {
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

    log::info!(
        "[collect_semantic_errors] filepath={}, no_core = {}",
        filepath,
        no_core
    );
    let build_options = BuildOptions {
        input_path: filepath.clone(),
        no_core,
        ..Default::default()
    };
    let driver = Driver::new(ray_paths);
    let frontend = match driver.build_frontend(&build_options, Some(overlays)) {
        Ok(frontend) => frontend,
        Err(errors) => return Ok((errors, None)),
    };

    let FrontendResult {
        module_path,
        tcx,
        ncx,
        srcmap,
        symbol_map,
        paths,
        definitions_by_path,
        definitions_by_id,
        errors,
        ..
    } = frontend;

    let mut node_type_info: HashMap<NodeId, TypeInfoSnapshot> = HashMap::new();
    for (node_id, scheme) in tcx.node_schemes.iter() {
        let (ty, is_scheme) = tcx
            .pretty_type_info_for_node(*node_id)
            .unwrap_or_else(|| (tcx.pretty_tys(scheme).to_string(), true));
        node_type_info.insert(*node_id, TypeInfoSnapshot { ty, is_scheme });
    }
    for (node_id, _) in tcx.node_tys.iter() {
        node_type_info.entry(*node_id).or_insert_with(|| {
            let (ty, is_scheme) = tcx
                .pretty_type_info_for_node(*node_id)
                .unwrap_or_else(|| ("<unknown>".to_string(), false));
            TypeInfoSnapshot { ty, is_scheme }
        });
    }

    let snapshot = AnalysisSnapshotData {
        module_path,
        entry_path: filepath.clone(),
        name_context: ncx,
        srcmap,
        node_type_info,
        symbol_map,
        definitions: definitions_by_path,
        definitions_by_id,
        module_paths: paths,
    };

    Ok((errors, Some(snapshot)))
}

fn dedup_diagnostics(mut diags: Vec<Diagnostic>) -> Vec<Diagnostic> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    #[allow(dead_code)]
    fn enable_debug_logs() {
        fern::Dispatch::new()
            .level(log::LevelFilter::Debug)
            .chain(std::io::stderr())
            .apply()
            .unwrap();
    }

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

    #[test]
    fn snapshot_tracks_distinct_types_for_shadowed_locals() {
        let uri = test_uri();
        let root = workspace_root();

        let result = collect(
            &uri,
            r#"fn main() {
    l = [1, 2]
    x = l.get(1)
    if some(x) = x {
        print(x)
    } else {
        print("none")
    }
}
"#,
            Some(&root),
            Some(&root),
        );

        let CollectResult::Diagnostics {
            diagnostics,
            snapshot,
        } = result
        else {
            panic!("expected diagnostics result")
        };

        assert!(
            diagnostics.is_empty(),
            "expected no diagnostics, got {diagnostics:?}"
        );

        let snapshot = snapshot.expect("expected semantic snapshot");

        // Line/col are 0-based. On the `if some(x) = x {` line, there are two
        // distinct `x` nodes that must have different types.
        let filepath = snapshot.entry_path.clone();
        let (pattern_node_id, _) = snapshot
            .srcmap
            .find_at_position(&filepath, 3, 12)
            .expect("expected node at pattern x");
        let (rhs_node_id, _) = snapshot
            .srcmap
            .find_at_position(&filepath, 3, 17)
            .expect("expected node at rhs x");

        let pattern_ty = snapshot
            .node_type_info
            .get(&pattern_node_id)
            .map(|info| info.ty.as_str())
            .expect("expected type for pattern x");
        let rhs_ty = snapshot
            .node_type_info
            .get(&rhs_node_id)
            .map(|info| info.ty.as_str())
            .expect("expected type for rhs x");

        assert!(
            pattern_ty.contains("int") && !pattern_ty.contains("nilable"),
            "expected pattern x to be int, got {pattern_ty}"
        );
        assert!(
            rhs_ty.contains("nilable[int]"),
            "expected rhs x to be nilable[int], got {rhs_ty}"
        );
    }
}
