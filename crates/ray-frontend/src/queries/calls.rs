use ray_query_macros::query;
use ray_shared::{local_binding::LocalBindingId, node_id::NodeId, pathlib::ItemPath, ty::Ty};
use ray_typing::{
    PatternKind, TypeCheckInput,
    context::{AssignLhs, ExprKind},
    tyctx::CallResolution,
    types::{Subst, TyScheme},
    unify::mgu,
};

use crate::{
    queries::{
        defs::{
            ImplsForType, def_for_path, impl_def, impls_for_type, trait_def, trait_impl_for_type,
        },
        deps::binding_group_for_def,
        resolve::resolve_builtin,
        typecheck::{inferred_local_type, ty_of, typecheck_group_input},
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
    let input = typecheck_group_input(db, group_id.clone());

    // Check if this node is an expression
    if let Some(expr_record) = input.expr_records.get(&node_id) {
        return match &expr_record.kind {
            ExprKind::BinaryOp {
                trait_fqn,
                method_fqn,
                operator,
                ..
            }
            | ExprKind::UnaryOp {
                trait_fqn,
                method_fqn,
                operator,
                ..
            } => resolve_op(db, trait_fqn, method_fqn, operator),
            ExprKind::Call { callee, .. } => resolve_call(db, callee, &input),
            ExprKind::Index { container, index } => {
                resolve_index_get(db, node_id, *container, *index)
            }
            ExprKind::Assign {
                lhs_pattern,
                lhs,
                rhs,
            } => {
                let AssignLhs::Index { container, index } = lhs else {
                    return None;
                };
                resolve_index_set(db, node_id, *lhs_pattern, *container, *index, *rhs, &input)
            }
            _ => None,
        };
    }

    // Check if this node is a pattern (for nested index patterns like `l[i]` in `l[i][j] = v`)
    if let Some(pattern_record) = input.pattern_records.get(&node_id) {
        return match &pattern_record.kind {
            PatternKind::Index { container, index } => {
                // This pattern needs Index::get resolution
                resolve_index_get(db, node_id, *container, *index)
            }
            _ => None,
        };
    }

    None
}

fn resolve_op(
    db: &Database,
    trait_fqn: &ItemPath,
    method_fqn: &ItemPath,
    operator: &NodeId,
) -> Option<CallResolution> {
    // Look up the trait definition
    let trait_target = def_for_path(db, trait_fqn.clone())?;
    let trait_definition = trait_def(db, trait_target)?;

    // Find the method in the trait
    let method_name = method_fqn.item_name()?;
    let method_info = trait_definition
        .methods
        .iter()
        .find(|m| m.name == method_name)?;

    // poly_callee_ty is the trait method's type scheme
    let poly_callee_ty = method_info.scheme.clone();

    // callee_ty is the instantiated type from typechecking
    let callee_mono_ty = ty_of(db, *operator)?;
    let callee_ty = TyScheme::from_mono(callee_mono_ty.clone());

    // Compute substitution via MGU
    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    // target is the method's DefTarget
    let target = method_info.target.clone();

    Some(CallResolution {
        target,
        poly_callee_ty,
        callee_ty,
        subst,
    })
}

fn resolve_call(db: &Database, callee: &NodeId, input: &TypeCheckInput) -> Option<CallResolution> {
    let callee_kind = input.expr_kind(*callee)?;
    let ExprKind::FieldAccess { recv, field } = callee_kind else {
        return None;
    };

    let recv_ty = ty_of(db, *recv)?;

    let recv_path = match &recv_ty {
        Ty::Ref(inner) => inner.item_path(),
        _ => recv_ty.item_path(),
    };
    let recv_path = recv_path?;

    let recv_target = def_for_path(db, recv_path.clone())?;

    let ImplsForType {
        inherent,
        trait_impls,
    } = impls_for_type(db, recv_target);

    let mut options = trait_impls
        .iter()
        .chain(inherent.iter())
        .filter_map(|target| impl_def(db, target.clone()))
        .filter_map(|impl_def| impl_def.find_method(field))
        .collect::<Vec<_>>();
    if let Some(method_info) = options.pop() {
        if !options.is_empty() {
            // Should we do something differently if there is ambiguity?
            return None;
        }

        let callee_ty = TyScheme::from_mono(ty_of(db, *callee).unwrap());
        let poly_callee_ty = method_info.scheme.clone();
        let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
            Ok((_, subst)) => subst,
            Err(_) => Subst::new(),
        };
        return Some(CallResolution {
            target: method_info.target,
            poly_callee_ty,
            callee_ty,
            subst,
        });
    }

    None
}

fn resolve_index_get(
    db: &Database,
    index_expr_id: NodeId,
    container_id: NodeId,
    index_id: NodeId,
) -> Option<CallResolution> {
    // Lookup the Index trait and find the "get" method info from the definition
    let file_id = container_id.owner.file;
    let index_trait_target = resolve_builtin(db, file_id, "Index".to_string())?;
    let index_trait_def = trait_def(db, index_trait_target.clone())?;
    let get_method_info = index_trait_def.find_method("get")?;

    // Get the method scheme and find the types of expressions
    let poly_callee_ty = get_method_info.scheme.clone();
    let container_ty = ty_of(db, container_id)?;
    let index_ty = ty_of(db, index_id)?;
    let result_ty = ty_of(db, index_expr_id)?;

    // Find the impl target for the container type
    let container_path = container_ty.item_path().cloned()?;
    let recv_target = def_for_path(db, container_path)?;
    let index_impl_target = trait_impl_for_type(db, recv_target, index_trait_target)?;
    let index_impl_def = impl_def(db, index_impl_target)?;
    let get_method_info = index_impl_def.find_method("get")?;

    // Construct the monomorphic function type
    let recv_ty = Ty::ref_of(container_ty);
    let callee_ty = TyScheme::from_mono(Ty::Func(vec![recv_ty, index_ty], Box::new(result_ty)));

    // Calculate the substitution from MGU of the monomorphic types
    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    Some(CallResolution {
        target: get_method_info.target,
        poly_callee_ty,
        callee_ty,
        subst,
    })
}

fn resolve_index_set(
    db: &Database,
    assign_expr_id: NodeId,
    _lhs_pattern_id: NodeId,
    container_binding: LocalBindingId,
    index_id: NodeId,
    rhs_id: NodeId,
    _input: &TypeCheckInput,
) -> Option<CallResolution> {
    // Lookup the Index trait and find the "set" method info from the definition
    let file_id = container_binding.owner.file;
    let index_trait_target = resolve_builtin(db, file_id, "Index".to_string())?;
    let index_trait_def = trait_def(db, index_trait_target.clone())?;
    let set_method_info = index_trait_def.find_method("set")?;

    // Get the method scheme and find the types of expressions
    let poly_callee_ty = set_method_info.scheme.clone();
    let container_ty = inferred_local_type(db, container_binding)?;
    let index_ty = ty_of(db, index_id)?;
    let rhs_ty = ty_of(db, rhs_id)?;
    let result_ty = ty_of(db, assign_expr_id)?;

    // Find the impl target for the container type
    let container_path = container_ty.item_path().cloned()?;
    let recv_target = def_for_path(db, container_path)?;
    let index_impl_target = trait_impl_for_type(db, recv_target, index_trait_target)?;
    let index_impl_def = impl_def(db, index_impl_target)?;
    let set_method_info = index_impl_def.find_method("set")?;

    // Construct the monomorphic function type: (*Container, Index, Elem) -> Elem?
    // The set method signature is: fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
    let recv_ty = Ty::ref_of(container_ty);
    let callee_ty = TyScheme::from_mono(Ty::Func(
        vec![recv_ty, index_ty, rhs_ty],
        Box::new(result_ty),
    ));

    // Calculate the substitution from MGU of the monomorphic types
    let subst = match mgu(poly_callee_ty.mono(), callee_ty.mono()) {
        Ok((_, subst)) => subst,
        Err(_) => Subst::new(),
    };

    Some(CallResolution {
        target: set_method_info.target,
        poly_callee_ty,
        callee_ty,
        subst,
    })
}

#[cfg(test)]
mod tests {
    use ray_shared::{
        def::DefHeader,
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
    };
    use ray_typing::{
        PatternKind,
        context::{AssignLhs, ExprKind},
    };

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
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
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

        if let Some(call_node_id) = call_node_id {
            let resolution = call_resolution(&db, call_node_id);
            assert!(
                resolution.is_none(),
                "Direct function calls should not produce call resolution"
            );
        }
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

        if let Some(literal_node_id) = literal_node_id {
            let resolution = call_resolution(&db, literal_node_id);
            assert!(
                resolution.is_none(),
                "Literal expressions should not produce call resolution"
            );
        }
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

        if let Some(binary_op_node_id) = binary_op_node_id {
            // Debug: print what the BinaryOp contains
            if let Some(record) = input.expr_records.get(&binary_op_node_id) {
                if let ExprKind::BinaryOp {
                    trait_fqn,
                    method_fqn,
                    ..
                } = &record.kind
                {
                    eprintln!("trait_fqn: {:?}", trait_fqn);
                    eprintln!("method_fqn: {:?}", method_fqn);
                }
            }

            let resolution = call_resolution(&db, binary_op_node_id);
            assert!(
                resolution.is_some(),
                "BinaryOp should produce call resolution"
            );
        }
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

        // Debug: print diagnostics
        eprintln!("All defs in file:");
        for def in &file_result.defs {
            eprintln!("  {} ({:?})", def.name, def.def_id);
        }
        eprintln!("Parse/transform errors: {:?}", file_result.errors);
        eprintln!("Lowering errors: {:?}", input.lowering_errors);

        // Debug: print all expr kinds
        for (id, record) in input.expr_records.iter() {
            eprintln!("  {:?}: {:?}", id, record.kind);
        }

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

        if let Some(method_call_node_id) = method_call_node_id {
            let resolution = call_resolution(&db, method_call_node_id);
            assert!(
                resolution.is_some(),
                "Method call should produce call resolution"
            );
        }
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

        if let Some(index_node_id) = index_node_id {
            let resolution = call_resolution(&db, index_node_id);
            assert!(
                resolution.is_some(),
                "Index expression should produce call resolution"
            );
        }
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

        if let Some(assign_node_id) = assign_node_id {
            let resolution = call_resolution(&db, assign_node_id);
            assert!(
                resolution.is_some(),
                "Index assignment should produce call resolution"
            );
        }
    }

    #[test]
    #[ignore = "Nested index patterns (m[0][1] = v) not yet implemented in lowering"]
    fn call_resolution_for_nested_index_pattern() {
        // Test nested index like l[i][j] = v where l[i] is a pattern needing Index::get
        let source = r#"
trait Index['a, 'el, 'idx] {
    fn get(self: *'a, idx: 'idx) -> 'el?
    fn set(self: *'a, idx: 'idx, el: 'el) -> 'el?
}

struct List { data: int }
struct Matrix { rows: List }

impl Index[Matrix, List, int] {
    fn get(self: *Matrix, idx: int) -> List? => nil
    fn set(self: *Matrix, idx: int, el: List) -> List? => nil
}

impl Index[List, int, int] {
    fn get(self: *List, idx: int) -> int? => nil
    fn set(self: *List, idx: int, el: int) -> int? => nil
}

fn test() {
    m = Matrix { rows: List { data: 0 } }
    m[0][1] = 42
}
"#;
        let (db, file_id) = setup_test_db(source);

        let file_result = file_ast(&db, file_id);
        let test_def = find_def_by_name(&file_result, "test").expect("Should have test function");

        let group_id = binding_group_for_def(&db, test_def.def_id);
        let input = typecheck_group_input(&db, group_id);

        // Find the outer Assign expression (for m[0][1] = 42)
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

        // The outer assignment should resolve to Index::set
        if let Some(assign_node_id) = assign_node_id {
            let resolution = call_resolution(&db, assign_node_id);
            assert!(
                resolution.is_some(),
                "Outer index assignment should produce call resolution"
            );
        }

        // Find the inner PatternKind::Index (for m[0])
        let inner_pattern_id = input.pattern_records.iter().find_map(|(id, record)| {
            if matches!(record.kind, PatternKind::Index { .. }) {
                return Some(*id);
            }
            None
        });

        assert!(
            inner_pattern_id.is_some(),
            "Should have an inner index pattern"
        );

        // The inner pattern should resolve to Index::get
        if let Some(inner_pattern_id) = inner_pattern_id {
            let resolution = call_resolution(&db, inner_pattern_id);
            assert!(
                resolution.is_some(),
                "Inner index pattern should produce call resolution"
            );
        }
    }
}
