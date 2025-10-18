use std::path::PathBuf;

use ray::{
    ast::Path,
    driver::RayPaths,
    errors::RayError,
    parse::{ParseOptions, Parser},
    pathlib::FilePath,
    sema::ModuleBuilder,
    span::{Source, SourceMap},
    typing::InferSystem,
};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range, Url};

pub enum CollectResult {
    Diagnostics(Vec<Diagnostic>),
    ToolchainMissing,
}

pub fn collect(
    uri: &Url,
    text: &str,
    workspace_root: Option<&FilePath>,
    toolchain_root: Option<&FilePath>,
) -> CollectResult {
    let filepath = to_filepath(uri);
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
        return CollectResult::Diagnostics(diagnostics);
    }

    match collect_semantic_errors(text, &filepath, workspace_root, toolchain_root) {
        Ok(semantic_errors) => {
            diagnostics.extend(
                semantic_errors
                    .into_iter()
                    .flat_map(|error| map_error(error, &filepath)),
            );
            CollectResult::Diagnostics(diagnostics)
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
) -> Result<Vec<RayError>, SemanticError> {
    let ray_paths = match RayPaths::discover(toolchain_root.cloned(), workspace_root) {
        Some(paths) => paths,
        None => return Err(SemanticError::ToolchainMissing),
    };

    let module_path = Path::from(filepath.clone());
    let mut include_paths = Vec::new();
    let c_include = ray_paths.get_c_includes_path();
    if c_include.exists() {
        include_paths.push(c_include);
    }

    let mut builder = ModuleBuilder::new(&ray_paths, include_paths, false);
    let scope = match builder.build_from_src(text.to_string(), module_path.clone()) {
        Ok(scope) => scope,
        Err(err) => return Ok(vec![err]),
    };

    let mut result = match builder.finish(&scope.path) {
        Ok(result) => result,
        Err(errors) => return Ok(errors),
    };

    let mut infer = InferSystem::new(&mut result.tcx, &mut result.ncx);
    let semantic = match infer.infer_ty(&result.module, &mut result.srcmap, result.defs) {
        Ok(_) => Vec::new(),
        Err(errors) => errors.into_iter().map(RayError::from).collect(),
    };

    Ok(semantic)
}

fn map_error(error: RayError, target: &FilePath) -> Vec<Diagnostic> {
    let RayError { msg, src, .. } = error;
    let mut diagnostics: Vec<Diagnostic> = src
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

    if diagnostics.is_empty() {
        diagnostics.push(Diagnostic {
            range: default_range(),
            severity: Some(DiagnosticSeverity::ERROR),
            code: None,
            code_description: None,
            source: Some("ray".to_string()),
            message: msg,
            related_information: None,
            tags: None,
            data: None,
        });
    }

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

fn span_to_range(span: ray::span::Span) -> Range {
    Range::new(pos_to_position(span.start), pos_to_position(span.end))
}

fn pos_to_position(pos: ray::span::Pos) -> Position {
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
            CollectResult::Diagnostics(diagnostics) => diagnostics,
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
}
