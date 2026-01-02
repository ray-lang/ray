use ray_core::sema::SymbolTarget;
use ray_shared::node_id::NodeId;
use ray_shared::pathlib::FilePath;
use ray_shared::span::Source;

use crate::diagnostics::AnalysisSnapshotData;

pub(crate) struct ResolvedSymbol {
    pub(crate) node_id: NodeId,
    pub(crate) source: Source,
    pub(crate) symbol_targets: Vec<SymbolTarget>,
}

pub(crate) fn resolve_symbol_at_position(
    snapshot: &AnalysisSnapshotData,
    filepath: &FilePath,
    line: usize,
    col: usize,
) -> Option<ResolvedSymbol> {
    let (node_id, source) = snapshot.srcmap.find_at_position(filepath, line, col)?;
    let symbol_targets = snapshot
        .symbol_map
        .get(&node_id)
        .map(|targets| targets.to_vec())
        .unwrap_or_default();
    Some(ResolvedSymbol {
        node_id,
        source,
        symbol_targets,
    })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use tower_lsp::lsp_types::Url;

    use crate::diagnostics::{CollectOptions, CollectResult, collect_with_options};
    use crate::symbols::resolve_symbol_at_position;

    use ray_shared::pathlib::FilePath;

    fn workspace_root() -> FilePath {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let workspace_root = manifest_dir
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root is available");
        FilePath::from(workspace_root.to_path_buf())
    }

    fn test_uri() -> Url {
        Url::parse("file:///symbols_test.ray").expect("valid file uri")
    }

    #[test]
    fn resolves_symbol_at_position() {
        let uri = test_uri();
        let root = workspace_root();
        let source = r#"fn foo() {
    foo()
}
"#;
        let result = collect_with_options(
            &uri,
            source,
            CollectOptions {
                force_no_core: true,
                workspace_root: Some(root.clone()),
                toolchain_root: Some(root),
            },
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
        let resolved = resolve_symbol_at_position(&snapshot, &snapshot.entry_path, 1, 4)
            .expect("expected resolved symbol");
        assert!(
            !resolved.symbol_targets.is_empty(),
            "expected symbol targets for foo() call"
        );
        assert!(
            resolved.source.span.is_some(),
            "expected source span for resolved symbol"
        );
    }

    #[test]
    fn resolves_scoped_access_call_symbol() {
        let uri = test_uri();
        let root = workspace_root();
        let source = r#"struct dict['k, 'v] { }

impl object dict['k, 'v] {
    static fn __h2(hash: u64) -> u8 { 0u8 }
}

fn main() {
    h2 = dict[int, int]::__h2(0u64)
}
"#;
        let result = collect_with_options(
            &uri,
            source,
            CollectOptions {
                force_no_core: true,
                workspace_root: Some(root.clone()),
                toolchain_root: Some(root),
            },
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
        let needle = "::__h2";
        let byte_offset = source
            .rfind(needle)
            .expect("expected scoped __h2 in source");
        let byte_offset = byte_offset + 2;
        let line = source[..byte_offset].bytes().filter(|&b| b == b'\n').count();
        let col = source[..byte_offset]
            .split('\n')
            .last()
            .unwrap_or_default()
            .len();
        let resolved = resolve_symbol_at_position(&snapshot, &snapshot.entry_path, line, col)
            .expect("expected resolved symbol");
        assert!(
            !resolved.symbol_targets.is_empty(),
            "expected symbol targets for scoped access call"
        );
    }
}
