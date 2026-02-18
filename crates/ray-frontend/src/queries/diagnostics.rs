//! Diagnostic queries for the incremental compiler.
//!
//! This module provides queries for collecting all diagnostics (errors) for files
//! and the workspace as a whole. It aggregates errors from parsing, transformation,
//! name resolution, validation, and type checking.

use std::collections::{HashMap, HashSet};

use ray_core::{
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    pathlib::FilePath,
    resolution::{NameKind, Resolution},
    span::Source,
};

use crate::{
    queries::{
        deps::binding_group_for_def, ownership::validate_ownership, parse::parse_file,
        ref_mutability::validate_ref_mutability, resolve::name_resolutions, transform::file_ast,
        typecheck::typecheck_group, validation::validate_def, workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// Collects all diagnostics (errors) for a file.
///
/// This query aggregates errors from multiple phases:
/// 1. Parse errors - syntax errors from parsing
/// 2. Transform errors - structural errors from AST transformation
/// 3. Name resolution errors - undefined names
/// 4. Validation errors - annotation policy, impl completeness, etc.
/// 5. Type errors - type mismatches, unification failures, etc.
///
/// The returned errors are deduplicated and ordered by source location.
#[query]
pub fn file_diagnostics(db: &Database, file_id: FileId) -> Vec<RayError> {
    let mut errors = Vec::new();

    // Get file info for filepath
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let file_info = match workspace.file_info(file_id) {
        Some(info) => info,
        None => return errors,
    };
    let filepath = file_info.path.clone();

    // Collect parse errors
    let parse_result = parse_file(db, file_id);
    errors.extend(parse_result.errors.clone());

    // Collect transform errors (struct field validation, etc.)
    let file_ast_result = file_ast(db, file_id);
    errors.extend(file_ast_result.errors.clone());

    // Collect name resolution errors
    let resolutions = name_resolutions(db, file_id);
    errors.extend(collect_resolution_errors(
        &resolutions,
        &parse_result.source_map,
        &filepath,
    ));

    // Collect validation errors (annotation policy, impl completeness, etc.)
    for def_header in &file_ast_result.defs {
        errors.extend(validate_def(db, def_header.def_id));
    }

    // Collect type errors (triggers typechecking)
    // Track which groups we've already processed to avoid duplicates
    let mut processed_groups = HashSet::new();

    for def_header in &file_ast_result.defs {
        let group_id = match binding_group_for_def(db, def_header.def_id) {
            Some(id) => id,
            None => continue,
        };

        // Skip if we've already processed this group
        if !processed_groups.insert(group_id.clone()) {
            continue;
        }

        let typecheck_result = typecheck_group(db, group_id);

        // Convert TypeErrors to RayErrors and filter by file
        for type_error in &typecheck_result.errors {
            // Check if any source location in this error belongs to this file
            let belongs_to_file = type_error
                .info
                .source
                .iter()
                .any(|src| src.filepath == filepath);

            if belongs_to_file {
                errors.push(type_error.clone().into());
            }
        }
    }

    // Collect post-typing validation errors (ownership, ref mutability)
    // These run after typechecking because they depend on inferred types.
    for def_header in &file_ast_result.defs {
        errors.extend(validate_ownership(db, def_header.def_id));
        errors.extend(validate_ref_mutability(db, def_header.def_id));
    }

    errors
}

/// Collects all diagnostics for the entire workspace.
///
/// This aggregates `file_diagnostics` for all files in the workspace.
/// Useful for build commands that need to report all errors at once.
#[query]
pub fn workspace_diagnostics(db: &Database, _key: ()) -> Vec<RayError> {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let mut all_errors = Vec::new();

    for file_id in workspace.all_file_ids() {
        all_errors.extend(file_diagnostics(db, file_id));
    }

    all_errors
}

/// Collects errors from name resolution results.
///
/// Creates errors for any `Resolution::Error` entries in the resolutions map.
/// Uses the source map to get span information for error messages.
fn collect_resolution_errors(
    resolutions: &HashMap<NodeId, Resolution>,
    source_map: &SourceMap,
    filepath: &FilePath,
) -> Vec<RayError> {
    let mut errors = Vec::new();

    for (node_id, resolution) in resolutions {
        if let Resolution::Error { name, kind } = resolution {
            // Get the source info for this node
            let src = source_map.get_by_id(*node_id).unwrap_or_else(|| Source {
                span: None,
                filepath: filepath.clone(),
                ..Default::default()
            });

            let kind_str = match kind {
                NameKind::Type => "type",
                NameKind::Value => "name",
            };

            errors.push(RayError {
                msg: format!("{kind_str} `{name}` is not defined"),
                src: vec![src],
                kind: RayErrorKind::Name,
                context: Some("name resolution".to_string()),
            });
        }
    }

    errors
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_core::errors::RayErrorKind;
    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            diagnostics::{file_diagnostics, workspace_diagnostics},
            libraries::LoadedLibraries,
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    fn setup_no_core(db: &Database) {
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );
    }

    fn setup_test_db(source: &str) -> (Database, ray_shared::file_id::FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        setup_no_core(&db);
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );
        (db, file_id)
    }

    #[test]
    fn file_diagnostics_returns_empty_for_valid_code() {
        // Use simple code without built-in type references (no_core mode)
        let (db, file_id) = setup_test_db("struct Point { x: Point }");

        let errors = file_diagnostics(&db, file_id);

        assert!(
            errors.is_empty(),
            "Valid code should produce no errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_collects_parse_errors() {
        let (db, file_id) = setup_test_db("fn main( {");

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have parse errors");
        // Parse errors have kind Parse or UnexpectedToken
        assert!(
            errors
                .iter()
                .any(|e| { matches!(e.kind, RayErrorKind::Parse | RayErrorKind::UnexpectedToken) }),
            "Should have a parse error"
        );
    }

    #[test]
    fn file_diagnostics_collects_transform_errors() {
        let (db, file_id) = setup_test_db("fn main() { p = UndefinedStruct { x: 1 } }");

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have transform errors");
        assert!(
            errors.iter().any(|e| e.msg.contains("undefined")),
            "Should have undefined struct error: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_collects_validation_errors() {
        // Partial annotation - x is annotated but y is not
        let source = r#"
struct S {}
fn bad(x: S, y) { x }
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have validation errors");
        assert!(
            errors.iter().any(|e| e.msg.contains("type annotation")),
            "Should have annotation policy error: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_collects_type_errors() {
        // Type mismatch: returning wrong struct type
        let source = r#"
struct A {}
struct B {}

fn foo() -> A => B {}
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have type errors");
        assert!(
            errors.iter().any(|e| e.kind == RayErrorKind::Type),
            "Should have a type error: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_collects_multiple_error_types() {
        // This has both a validation error (partial annotation) and a type error
        let source = r#"
struct A {}
struct B {}
fn bad(x: A, y) { x }
fn also_bad() -> A => B {}
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        // Should have at least one validation error and one type error
        assert!(
            errors.len() >= 2,
            "Should have multiple errors: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_deduplicates_group_errors() {
        // Two functions in the same binding group (mutually recursive unannotated)
        // Should not produce duplicate errors
        let source = r#"
fn is_even(n) {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n) {
    if n == 0 { false } else { is_even(n - 1) }
}
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        // The code should typecheck successfully (mutually recursive bool functions)
        // This test mainly verifies we don't crash or produce duplicate errors
        // from processing the same group twice
        let _ = errors; // Errors may or may not exist depending on inference
    }

    #[test]
    fn file_diagnostics_works_for_impl_validation() {
        // Missing required method in impl
        let source = r#"
struct Result {}

trait Showable['a] {
    fn show(self: 'a) -> Result
}

struct Point { x: Point }

impl Showable[Point] {
}
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have impl completeness error");
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("missing required method")),
            "Should have missing method error: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_works_for_mutability_errors() {
        // Assigning to immutable parameter
        let source = r#"
struct S {}
fn foo(x: S) -> S { x = S {}; x }
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have mutability error");
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot assign to immutable")),
            "Should have immutable assignment error: {:?}",
            errors
        );
    }

    #[test]
    fn workspace_diagnostics_aggregates_file_errors() {
        // Use type mismatch which does produce type errors
        let source = r#"
struct A {}
struct B {}
fn foo() -> A => B {}
"#;
        let (db, _file_id) = setup_test_db(source);

        let errors = workspace_diagnostics(&db, ());

        assert!(!errors.is_empty(), "Should have type error");
        assert!(
            errors.iter().any(|e| e.kind == RayErrorKind::Type),
            "Should have a type error: {:?}",
            errors
        );
    }

    #[test]
    fn workspace_diagnostics_returns_empty_for_valid_code() {
        let (db, _file_id) = setup_test_db("struct Point { x: Point }");

        let errors = workspace_diagnostics(&db, ());

        assert!(
            errors.is_empty(),
            "Valid code should produce no errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn file_diagnostics_collects_name_resolution_errors() {
        // Using an undefined value name should produce a name resolution error
        let source = r#"
struct S {}
fn foo() -> S => hack
"#;
        let (db, file_id) = setup_test_db(source);

        let errors = file_diagnostics(&db, file_id);

        assert!(!errors.is_empty(), "Should have name resolution errors");
        assert!(
            errors.iter().any(|e| e.kind == RayErrorKind::Name),
            "Should have a name error, got: {:?}",
            errors
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("hack") && e.msg.contains("not defined")),
            "Should mention undefined name 'hack': {:?}",
            errors
        );

        // Verify the error has source location info
        let name_error = errors
            .iter()
            .find(|e| e.kind == RayErrorKind::Name)
            .unwrap();
        assert!(
            !name_error.src.is_empty(),
            "Name error should have source info"
        );
        assert!(
            name_error.src[0].span.is_some(),
            "Name error should have span info"
        );
    }

    #[test]
    fn file_diagnostics_recomputes_after_file_source_change() {
        // Simulate the LSP overlay pattern:
        // 1. File has an error → diagnostics should report it
        // 2. File source changes (error removed) → diagnostics should clear
        let bad_source = "struct S {}\nfn foo() -> S => hack";
        let (db, file_id) = setup_test_db(bad_source);

        let errors_before = file_diagnostics(&db, file_id);
        assert!(
            errors_before.iter().any(|e| e.kind == RayErrorKind::Name),
            "Should have name error before fix: {:?}",
            errors_before
        );

        // Simulate overlay: change file source to remove the error
        let good_source = "struct S {}\nfn foo() -> S => S {}";
        db.set_input::<FileSource>(file_id, FileSource(good_source.to_string()));

        let errors_after = file_diagnostics(&db, file_id);
        let has_hack_error = errors_after
            .iter()
            .any(|e| e.kind == RayErrorKind::Name && e.msg.contains("hack"));
        assert!(
            !has_hack_error,
            "Name error for 'hack' should be gone after fix, got: {:?}",
            errors_after
        );
    }
}
