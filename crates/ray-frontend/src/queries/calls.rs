use ray_query_macros::query;
use ray_shared::{node_id::NodeId, ty::Ty};
use ray_typing::{
    context::{AssignLhs, ExprKind},
    tyctx::CallResolution,
    types::{Subst, TyScheme},
    unify::mgu,
};

use crate::{
    queries::{
        deps::binding_group_for_def,
        typecheck::{ty_of, typecheck_group, typecheck_group_input},
    },
    query::{Database, Query},
};

/// Returns resolution information for a call expression that required method/trait resolution.
///
/// This includes:
/// - Method calls (`x.method()`)
/// - Operator calls (`a + b`)
/// - Index expressions (`a[i]`)
///
/// Returns `None` for direct function calls that don't go through method resolution.
///
/// **Dependencies**: `binding_group_for_def(node_id.owner)`, `typecheck_group(BindingGroupId)`
#[query]
pub fn call_resolution(db: &Database, node_id: NodeId) -> Option<CallResolution> {
    let def_id = node_id.owner;
    let group_id = binding_group_for_def(db, def_id);
    let result = typecheck_group(db, group_id.clone());
    let input = typecheck_group_input(db, group_id);

    // Look up the method resolution from the side-table populated by the solver
    let resolution_info = result.method_resolutions.get(&node_id)?;
    let poly_callee_ty = resolution_info.poly_scheme.clone();

    // Compute callee_ty based on expression kind
    let expr_record = input.expr_records.get(&node_id)?;
    let callee_ty = match &expr_record.kind {
        ExprKind::BinaryOp { operator, .. } | ExprKind::UnaryOp { operator, .. } => {
            TyScheme::from_mono(ty_of(db, *operator)?)
        }
        ExprKind::Call { callee, .. } => TyScheme::from_mono(ty_of(db, *callee)?),
        ExprKind::Index { container, index } => {
            let container_ty = ty_of(db, *container)?;
            let index_ty = ty_of(db, *index)?;
            let result_ty = ty_of(db, node_id)?;
            let recv_ty = Ty::ref_of(container_ty);
            TyScheme::from_mono(Ty::Func(vec![recv_ty, index_ty], Box::new(result_ty)))
        }
        ExprKind::Assign { lhs, rhs, .. } => {
            let AssignLhs::Index { container, index } = lhs else {
                return None;
            };
            let container_ty = ty_of(db, *container)?;
            let index_ty = ty_of(db, *index)?;
            let rhs_ty = ty_of(db, *rhs)?;
            let result_ty = ty_of(db, node_id)?;
            let recv_ty = Ty::ref_of(container_ty);
            TyScheme::from_mono(Ty::Func(
                vec![recv_ty, index_ty, rhs_ty],
                Box::new(result_ty),
            ))
        }
        _ => return None,
    };

    // Compute substitution via MGU
    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    Some(CallResolution {
        trait_target: resolution_info.trait_target.clone(),
        impl_target: resolution_info.impl_target.clone(),
        poly_callee_ty,
        callee_ty,
        subst,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefHeader,
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
    };
    use ray_typing::context::{AssignLhs, ExprKind};

    use crate::{
        queries::{
            calls::call_resolution,
            deps::binding_group_for_def,
            libraries::LoadedLibraries,
            transform::{FileAst, file_ast},
            typecheck::typecheck_group_input,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    fn setup_test_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, source.to_string());
        (db, file_id)
    }

    fn find_def_by_name<'a>(file_result: &'a FileAst, name: &str) -> Option<&'a DefHeader> {
        file_result.defs.iter().find(|d| d.name == name)
    }

    #[test]
    fn call_resolution_returns_none_for_direct_function_call() {
        let source = r#"
fn helper(x: int) -> int => x
fn main() -> int => helper(42)
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let main_def = find_def_by_name(&file_result, "main").expect("Should have main function");

        let group_id = binding_group_for_def(&db, main_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        let call_node_id = input
            .expr_records
            .iter()
            .find(|(_, record)| matches!(record.kind, ExprKind::Call { .. }))
            .map(|(id, _)| *id);

        assert!(call_node_id.is_some(), "cannot find call node ID");

        let resolution = call_resolution(&db, call_node_id.unwrap());
        assert!(
            resolution.is_none(),
            "Direct function calls should not produce call resolution"
        );
    }

    #[test]
    fn call_resolution_returns_none_for_non_call_expression() {
        let source = r#"
fn get_value() -> int => 42
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let func_def =
            find_def_by_name(&file_result, "get_value").expect("Should have get_value function");

        let group_id = binding_group_for_def(&db, func_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        let literal_node_id = input
            .expr_records
            .iter()
            .find(|(_, record)| matches!(record.kind, ExprKind::LiteralInt))
            .map(|(id, _)| *id);

        assert!(literal_node_id.is_some(), "cannot find literal node ID");

        let resolution = call_resolution(&db, literal_node_id.unwrap());
        assert!(
            resolution.is_none(),
            "Literal expressions should not produce call resolution"
        );
    }

    #[test]
    fn call_resolution_for_binary_op() {
        // Define Add trait with operator method
        let source = r#"
trait Add['a, 'b, 'c] {
    fn +(a: 'a, b: 'b) -> 'c
}

impl Add[int, int, int] {
    fn +(a: int, b: int) -> int => a
}

fn test() -> int => 1 + 2
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let test_def = find_def_by_name(&file_result, "test").expect("Should have test function");

        let group_id = binding_group_for_def(&db, test_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        // Find the BinaryOp expression
        let binary_op_node_id = input
            .expr_records
            .iter()
            .find(|(_, record)| matches!(record.kind, ExprKind::BinaryOp { .. }))
            .map(|(id, _)| *id);

        assert!(
            binary_op_node_id.is_some(),
            "Should have a BinaryOp expression"
        );

        let resolution = call_resolution(&db, binary_op_node_id.unwrap());
        assert!(
            resolution.is_some(),
            "BinaryOp should produce call resolution"
        );

        let resolution = resolution.unwrap();

        // Binary operators resolve through traits, so both targets should be set
        assert!(
            resolution.trait_target.is_some(),
            "Binary op should have trait_target (Add::+)"
        );
        assert!(
            resolution.impl_target.is_some(),
            "Binary op should have impl_target (Add[int,int,int]::+)"
        );

        // target() prefers impl_target when available
        assert_eq!(
            resolution.target(),
            resolution.impl_target.as_ref(),
            "target() should prefer impl_target"
        );
    }

    #[test]
    fn call_resolution_for_method_call() {
        // Define a struct with an inherent method
        let source = r#"
struct Point { x: int, y: int }

impl object Point {
    fn magnitude(self: *Point) -> int => self.x
}

fn test() -> int {
    p = Point { x: 3, y: 4 }
    p.magnitude()
}
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let test_def = find_def_by_name(&file_result, "test").expect("Should have test function");

        let group_id = binding_group_for_def(&db, test_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        // Find a Call expression with a FieldAccess callee (method call pattern)
        let method_call_node_id = input.expr_records.iter().find_map(|(id, record)| {
            if let ExprKind::Call { callee, .. } = &record.kind {
                if let Some(callee_record) = input.expr_records.get(callee) {
                    if matches!(callee_record.kind, ExprKind::FieldAccess { .. }) {
                        return Some(*id);
                    }
                }
            }
            None
        });

        assert!(
            method_call_node_id.is_some(),
            "Should have a method call expression"
        );

        let resolution = call_resolution(&db, method_call_node_id.unwrap());
        assert!(
            resolution.is_some(),
            "Method call should produce call resolution"
        );

        let resolution = resolution.unwrap();

        // Inherent methods don't go through traits
        assert!(
            resolution.trait_target.is_none(),
            "Inherent method should not have trait_target"
        );
        assert!(
            resolution.impl_target.is_some(),
            "Inherent method should have impl_target (Point::magnitude)"
        );

        // The target() method should return the impl target
        assert_eq!(
            resolution.target(),
            resolution.impl_target.as_ref(),
            "target() should return impl_target for inherent methods"
        );
    }

    #[test]
    fn call_resolution_for_index_get() {
        // Define Index trait and impl
        let source = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct List { data: int }

impl Index[List, int, int] {
    fn get(self: *List, idx: int) -> int? => nil
    fn set(self: *List, idx: int, el: int) -> int? => nil
}

fn test() -> int? {
    l = List { data: 0 }
    l[0]
}
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let test_def = find_def_by_name(&file_result, "test").expect("Should have test function");

        let group_id = binding_group_for_def(&db, test_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        // Find the Index expression
        let index_node_id = input
            .expr_records
            .iter()
            .find(|(_, record)| matches!(record.kind, ExprKind::Index { .. }))
            .map(|(id, _)| *id);

        assert!(index_node_id.is_some(), "Should have an Index expression");

        let resolution = call_resolution(&db, index_node_id.unwrap());
        assert!(
            resolution.is_some(),
            "Index expression should produce call resolution"
        );

        let resolution = resolution.unwrap();

        // Index operations resolve through the Index trait
        assert!(
            resolution.trait_target.is_some(),
            "Index get should have trait_target (Index::get)"
        );
        assert!(
            resolution.impl_target.is_some(),
            "Index get should have impl_target (Index[List,int,int]::get)"
        );

        // The target() method should return the impl target (more specific)
        assert_eq!(
            resolution.target(),
            resolution.impl_target.as_ref(),
            "target() should prefer impl_target"
        );
    }

    #[test]
    fn call_resolution_for_index_set() {
        // Define Index trait and impl
        let source = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct List { data: int }

impl Index[List, int, int] {
    fn get(self: *List, idx: int) -> int? => nil
    fn set(self: *List, idx: int, el: int) -> int? => nil
}

fn test() -> int? {
    l = List { data: 0 }
    l[0] = 42
}
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let test_def = find_def_by_name(&file_result, "test").expect("Should have test function");

        let group_id = binding_group_for_def(&db, test_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        // Find the Assign expression with Index LHS
        let assign_node_id = input.expr_records.iter().find_map(|(id, record)| {
            if let ExprKind::Assign { lhs, .. } = &record.kind {
                if matches!(lhs, AssignLhs::Index { .. }) {
                    return Some(*id);
                }
            }
            None
        });

        assert!(
            assign_node_id.is_some(),
            "Should have an index assignment expression"
        );

        let resolution = call_resolution(&db, assign_node_id.unwrap());
        assert!(
            resolution.is_some(),
            "Index assignment should produce call resolution"
        );

        let resolution = resolution.unwrap();

        // Index set operations resolve through the Index trait
        assert!(
            resolution.trait_target.is_some(),
            "Index set should have trait_target (Index::set)"
        );
        assert!(
            resolution.impl_target.is_some(),
            "Index set should have impl_target (Index[List,int,int]::set)"
        );

        // The target() method should return the impl target (more specific)
        assert_eq!(
            resolution.target(),
            resolution.impl_target.as_ref(),
            "target() should prefer impl_target"
        );
    }
}
