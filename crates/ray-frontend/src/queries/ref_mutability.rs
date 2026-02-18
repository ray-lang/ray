//! Post-typing validation for reference mutability.
//!
//! Validates that assignments do not write through shared (`*T`) or
//! identity (`id *T`) references. This runs after type inference so
//! inferred types are available.

use std::collections::HashMap;

use ray_core::{
    ast::{Assign, Expr, Node, Pattern, WalkItem, walk_decl},
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::DefId, local_binding::LocalBindingId, node_id::NodeId, pathlib::FilePath,
    resolution::Resolution, span::Source, ty::Ty,
};

use crate::{
    queries::{
        defs::find_def_ast, resolve::name_resolutions, transform::file_ast,
        typecheck::inferred_local_type,
    },
    query::{Database, Query},
};

/// Validate that assignments do not write through shared or identity references.
///
/// Walks the AST looking for:
/// - `p.field = rhs` where `p: *T` or `p: id *T` → error
/// - `*p = rhs` where `p: *T` or `p: id *T` → error
#[query]
pub fn validate_ref_mutability(db: &Database, def_id: DefId) -> Vec<RayError> {
    let file_result = file_ast(db, def_id.file);

    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return vec![];
    };

    let Some(def_ast) = find_def_ast(&file_result.ast.decls, def_header.root_node) else {
        return vec![];
    };

    let filepath = file_result.ast.filepath.clone();
    let resolutions = name_resolutions(db, def_id.file);
    let mut errors = Vec::new();

    for item in walk_decl(def_ast) {
        let WalkItem::Expr(expr) = item else {
            continue;
        };

        let Expr::Assign(assign) = &expr.value else {
            continue;
        };

        check_assign_ref_mutability(
            db,
            assign,
            &resolutions,
            &filepath,
            &file_result.source_map,
            &mut errors,
        );
    }

    errors
}

/// Check if an assignment's LHS writes through a non-mutable reference.
fn check_assign_ref_mutability(
    db: &Database,
    assign: &Assign,
    resolutions: &HashMap<NodeId, Resolution>,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    match &assign.lhs.value {
        Pattern::Dot(base_pat, _field) => {
            if let Some(local_id) = resolve_pattern_to_local(base_pat, resolutions) {
                check_ref_write_allowed(db, local_id, &assign.lhs, filepath, srcmap, errors);
            }
        }
        Pattern::Deref(inner_name) => {
            if let Some(Resolution::Local(local_id)) = resolutions.get(&inner_name.id) {
                check_ref_write_allowed(db, *local_id, &assign.lhs, filepath, srcmap, errors);
            }
        }
        _ => {}
    }
}

/// Resolve a pattern to a LocalBindingId, if it's a simple name.
fn resolve_pattern_to_local(
    pat: &Node<Pattern>,
    resolutions: &HashMap<NodeId, Resolution>,
) -> Option<LocalBindingId> {
    match &pat.value {
        Pattern::Name(_) => match resolutions.get(&pat.id) {
            Some(Resolution::Local(local_id)) => Some(*local_id),
            _ => None,
        },
        Pattern::Dot(base, _) => resolve_pattern_to_local(base, resolutions),
        _ => None,
    }
}

/// Check whether writing through a reference is allowed.
/// Emits an error if the binding's type is `*T` (shared) or `id *T` (identity).
fn check_ref_write_allowed(
    db: &Database,
    local_id: LocalBindingId,
    lhs: &Node<Pattern>,
    filepath: &FilePath,
    srcmap: &SourceMap,
    errors: &mut Vec<RayError>,
) {
    let Some(ty) = inferred_local_type(db, local_id) else {
        return;
    };

    match &ty {
        Ty::Ref(_) => {
            errors.push(RayError {
                msg: "cannot assign through shared reference `*T`".to_string(),
                src: vec![Source {
                    span: Some(srcmap.span_of(lhs)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("reference mutability validation".to_string()),
            });
        }
        Ty::IdRef(_) => {
            errors.push(RayError {
                msg: "cannot access fields through identity reference `id *T`".to_string(),
                src: vec![Source {
                    span: Some(srcmap.span_of(lhs)),
                    filepath: filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("reference mutability validation".to_string()),
            });
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::pathlib::{FilePath, ModulePath};

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            parse::parse_file,
            ref_mutability::validate_ref_mutability,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn validate_ref_mutability_error_for_assign_through_shared_ref() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int }

fn bad(p: *Point) {
    p.x = 5
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let bad_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "bad")
            .expect("should find bad function");

        let errors = validate_ref_mutability(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for assignment through shared reference"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("shared reference")),
            "Error should mention shared reference: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ref_mutability_no_error_for_assign_through_mut_ref() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
struct Point { x: int }

fn ok(p: *mut Point) {
    p.x = 5
}
"#;
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );

        let parse_result = parse_file(&db, file_id);
        let ok_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "ok")
            .expect("should find ok function");

        let errors = validate_ref_mutability(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for assignment through *mut ref, got: {:?}",
            errors
        );
    }
}
