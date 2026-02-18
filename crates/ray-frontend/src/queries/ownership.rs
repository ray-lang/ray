//! Post-typing validation for `*mut T` ownership tracking.
//!
//! Tracks the state of `*mut T` variables and reports errors for
//! use-after-consume. Consumption occurs when `freeze(x)` is called
//! or when a `*mut T` is passed to a `move` parameter.

use std::collections::{HashMap, HashSet};

use ray_core::{
    ast::{BuiltinKind, Call, CurlyElement, Decl, Expr, Node},
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::DefId, file_id::FileId, local_binding::LocalBindingId, node_id::NodeId, pathlib::FilePath,
    resolution::DefTarget, span::Source,
};

use crate::{
    queries::{
        bindings::local_binding_for_node,
        defs::{find_def_ast, func_def},
        resolve::name_resolutions,
        transform::file_ast,
        typecheck::inferred_local_type,
    },
    query::{Database, Query},
};

/// Validate ownership rules for `*mut T` variables in a definition.
///
/// This runs after type inference. It tracks the state of `*mut T` variables
/// and reports errors for use-after-consume.
///
/// Consumption occurs when:
/// - `freeze(x)` is called (converts `*mut T` to `*T`)
/// - A `*mut T` is passed to a `move` parameter
#[query]
pub fn validate_ownership(db: &Database, def_id: DefId) -> Vec<RayError> {
    let file_result = file_ast(db, def_id.file);

    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return vec![];
    };

    let Some(def_ast) = find_def_ast(&file_result.ast.decls, def_header.root_node) else {
        return vec![];
    };

    let filepath = file_result.ast.filepath.clone();

    let mut ctx = OwnershipCtx::new(db, def_id.file, &filepath, &file_result.source_map);

    // Get the function body to analyze
    match &def_ast.value {
        Decl::Func(func) => {
            if let Some(body) = &func.body {
                ctx.visit_expr(body);
            }
        }
        _ => {}
    }

    ctx.errors
}

/// State of a `*mut T` variable during ownership analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VarState {
    /// The variable is alive and usable.
    Alive,
    /// The variable has been consumed (by freeze or move).
    Consumed,
}

/// A path identifying a borrow target, used for conflict detection.
///
/// Examples: `p` → `(p_id, [])`, `p.x` → `(p_id, ["x"])`, `p.x.y` → `(p_id, ["x", "y"])`
#[derive(Clone, Debug)]
struct BorrowPath {
    /// The root variable being borrowed.
    root: LocalBindingId,
    /// Field path from the root (empty for a whole-variable borrow).
    fields: Vec<String>,
}

impl BorrowPath {
    /// Check whether two borrow paths overlap (conflict).
    ///
    /// Two paths conflict if one is a prefix of the other:
    /// - `p` and `p.x` overlap (borrowing `p` covers `p.x`)
    /// - `p.x` and `p.y` are disjoint (different field at the same level)
    /// - `p.x` and `p.x` overlap (same path)
    fn overlaps(&self, other: &BorrowPath) -> bool {
        if self.root != other.root {
            return false;
        }
        let min_len = self.fields.len().min(other.fields.len());
        // Check that the shared prefix matches
        for i in 0..min_len {
            if self.fields[i] != other.fields[i] {
                return false;
            }
        }
        // If all shared components match and one is a prefix of the other, they overlap
        true
    }

    fn display_path(&self, name: Option<&str>) -> String {
        let root = name.unwrap_or("?");
        if self.fields.is_empty() {
            root.to_string()
        } else {
            format!("{}.{}", root, self.fields.join("."))
        }
    }
}

/// Context for tracking `*mut T` variable ownership.
struct OwnershipCtx<'a> {
    db: &'a Database,
    file_id: FileId,
    filepath: &'a FilePath,
    srcmap: &'a SourceMap,
    /// Maps tracked `*mut T` variables to their current state.
    var_states: HashMap<LocalBindingId, VarState>,
    errors: Vec<RayError>,
}

impl<'a> OwnershipCtx<'a> {
    fn new(
        db: &'a Database,
        file_id: FileId,
        filepath: &'a FilePath,
        srcmap: &'a SourceMap,
    ) -> Self {
        Self {
            db,
            file_id,
            filepath,
            srcmap,
            var_states: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// Check if a local binding has `*mut T` type, and start tracking it if so.
    fn ensure_tracked(&mut self, local_id: LocalBindingId) {
        if self.var_states.contains_key(&local_id) {
            return;
        }
        let Some(ty) = inferred_local_type(self.db, local_id) else {
            return;
        };
        if ty.is_mut_ref() {
            self.var_states.insert(local_id, VarState::Alive);
        }
    }

    /// Record a use of a variable. If it was consumed, emit an error.
    fn record_use(&mut self, local_id: LocalBindingId, expr: &Node<Expr>) {
        self.ensure_tracked(local_id);
        if self.var_states.get(&local_id) == Some(&VarState::Consumed) {
            let msg = if let Some(name) = expr.get_name() {
                format!("use of consumed `*mut` value `{}`", name)
            } else {
                "use of consumed `*mut` value".to_string()
            };

            self.errors.push(RayError {
                msg,
                src: vec![Source {
                    span: Some(self.srcmap.span_of(expr)),
                    filepath: self.filepath.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Type,
                context: Some("ownership validation".to_string()),
            });
        }
    }

    /// Mark a variable as consumed.
    fn consume(&mut self, local_id: LocalBindingId) {
        self.ensure_tracked(local_id);
        if self.var_states.contains_key(&local_id) {
            self.var_states.insert(local_id, VarState::Consumed);
        }
    }

    /// Save the current state for branching.
    fn save_state(&self) -> HashMap<LocalBindingId, VarState> {
        self.var_states.clone()
    }

    /// Merge two branch states: if consumed in either branch, mark as consumed.
    fn merge_states(
        &mut self,
        state_a: &HashMap<LocalBindingId, VarState>,
        state_b: &HashMap<LocalBindingId, VarState>,
    ) {
        let all_keys: HashSet<_> = state_a.keys().chain(state_b.keys()).collect();
        for key in all_keys {
            let a = state_a.get(key).copied().unwrap_or(VarState::Alive);
            let b = state_b.get(key).copied().unwrap_or(VarState::Alive);
            let merged = if a == VarState::Consumed || b == VarState::Consumed {
                VarState::Consumed
            } else {
                VarState::Alive
            };
            self.var_states.insert(*key, merged);
        }
    }

    /// Check if any arguments to a call are passed to `move` parameters,
    /// and if so, consume the corresponding `*mut T` variables.
    fn check_move_params(&mut self, call: &Call) {
        let callee_id = call.call_resolution_id();
        let Some(target) = self.resolve_callee_target(self.file_id, callee_id) else {
            return;
        };
        let Some(fdef) = func_def(&self.db, target) else {
            return;
        };

        // Method calls have an implicit self parameter
        let param_offset = if call.is_method_call() { 1 } else { 0 };

        for (i, arg) in call.args.items.iter().enumerate() {
            let param_idx = i + param_offset;
            let Some(param) = fdef.params.get(param_idx) else {
                continue;
            };
            if !param.is_move {
                continue;
            }
            // This argument is passed to a `move` parameter — consume it.
            if let Some(local_id) = local_binding_for_node(&self.db, arg.id) {
                self.consume(local_id);
            }
        }
    }

    /// Extract a borrow path from an argument expression.
    ///
    /// Returns `Some(BorrowPath)` if the expression is a `*mut T` variable
    /// (possibly with field access), `None` otherwise.
    fn extract_borrow_path(&self, expr: &Node<Expr>) -> Option<BorrowPath> {
        match &expr.value {
            Expr::Name(_) => {
                let local_id = local_binding_for_node(self.db, expr.id)?;
                let ty = inferred_local_type(self.db, local_id)?;
                if ty.is_mut_ref() {
                    Some(BorrowPath {
                        root: local_id,
                        fields: vec![],
                    })
                } else {
                    None
                }
            }
            Expr::Dot(dot) => {
                let mut path = self.extract_borrow_path(&dot.lhs)?;
                path.fields.push(dot.rhs.value.to_string());
                Some(path)
            }
            _ => None,
        }
    }

    /// Check for conflicting borrows among the arguments of a single call.
    ///
    /// Two `*mut T` arguments conflict if their borrow paths overlap:
    /// - Same variable passed twice as `*mut T` → conflict
    /// - `p.x` and `p` → conflict (overlapping)
    /// - `p.x` and `p.y` → OK (disjoint fields)
    fn check_borrow_conflicts(&mut self, call: &Call) {
        // Collect borrow paths for all *mut T arguments
        let mut borrows: Vec<(BorrowPath, &Node<Expr>)> = Vec::new();

        for arg in &call.args.items {
            if let Some(path) = self.extract_borrow_path(arg) {
                borrows.push((path, arg));
            }
        }

        // Check all pairs for overlap
        for i in 0..borrows.len() {
            for j in (i + 1)..borrows.len() {
                let (path_a, expr_a) = &borrows[i];
                let (path_b, expr_b) = &borrows[j];

                if path_a.overlaps(path_b) {
                    let display_a = path_a.display_path(expr_a.get_name().as_deref());
                    let display_b = path_b.display_path(expr_b.get_name().as_deref());

                    self.errors.push(RayError {
                        msg: format!(
                            "conflicting borrows: `{}` and `{}` overlap",
                            display_a, display_b
                        ),
                        src: vec![
                            Source {
                                span: Some(self.srcmap.span_of(*expr_a)),
                                filepath: self.filepath.clone(),
                                ..Default::default()
                            },
                            Source {
                                span: Some(self.srcmap.span_of(*expr_b)),
                                filepath: self.filepath.clone(),
                                ..Default::default()
                            },
                        ],
                        kind: RayErrorKind::Type,
                        context: Some("borrow conflict".to_string()),
                    });
                }
            }
        }
    }

    /// Resolve a callee NodeId to its DefTarget.
    fn resolve_callee_target(&self, file_id: FileId, callee_id: NodeId) -> Option<DefTarget> {
        let resolutions = name_resolutions(&self.db, file_id);
        resolutions.get(&callee_id)?.to_def_target()
    }

    /// Recursively visit an expression, tracking `*mut T` ownership state.
    fn visit_expr(&mut self, expr: &Node<Expr>) {
        match &expr.value {
            Expr::Block(block) => {
                for stmt in &block.stmts {
                    self.visit_expr(stmt);
                }
            }
            Expr::Assign(assign) => {
                // Visit the RHS first (it's evaluated before the binding)
                self.visit_expr(&assign.rhs);

                // If the LHS is a new binding and the RHS is a box/new,
                // the variable will be tracked when first used (via ensure_tracked).
                // We don't need to explicitly register it here — the type system
                // already knows it's *mut T.
            }
            Expr::BuiltinCall(bc) => {
                match bc.kind {
                    BuiltinKind::Freeze => {
                        // freeze(x) consumes x
                        if let Some(local_id) = local_binding_for_node(self.db, bc.arg.id) {
                            self.record_use(local_id, &bc.arg);
                            self.consume(local_id);
                        } else {
                            self.visit_expr(&bc.arg);
                        }
                    }
                    BuiltinKind::Id | BuiltinKind::Upgrade => {
                        self.visit_expr(&bc.arg);
                    }
                }
            }
            Expr::Name(_) => {
                // A use of a variable — check if it's consumed
                if let Some(local_id) = local_binding_for_node(self.db, expr.id) {
                    self.record_use(local_id, expr);
                }
            }
            Expr::If(if_expr) => {
                // Visit condition (in the pre-branch context)
                self.visit_expr(&if_expr.cond);

                // Fork state for branches
                let state_before = self.save_state();

                // Visit then-branch
                self.visit_expr(&if_expr.then);
                let state_then = self.save_state();

                // Restore and visit else-branch
                self.var_states = state_before;
                if let Some(els) = &if_expr.els {
                    self.visit_expr(els);
                }
                let state_else = self.save_state();

                // Merge: consumed in either branch → consumed
                self.merge_states(&state_then, &state_else);
            }
            Expr::Call(call) => {
                self.visit_expr(&call.callee);
                for arg in &call.args.items {
                    self.visit_expr(arg);
                }
                // Check for conflicting borrows among *mut T arguments.
                self.check_borrow_conflicts(call);
                // Check for `move` parameters that consume the argument.
                // Resolve the callee to its function AST to access is_move() flags.
                self.check_move_params(call);
            }
            Expr::Dot(dot) => {
                self.visit_expr(&dot.lhs);
            }
            Expr::BinOp(binop) => {
                self.visit_expr(&binop.lhs);
                self.visit_expr(&binop.rhs);
            }
            Expr::UnaryOp(unop) => {
                self.visit_expr(&unop.expr);
            }
            Expr::Sequence(seq) => {
                for item in &seq.items {
                    self.visit_expr(item);
                }
            }
            Expr::Tuple(tup) => {
                for item in &tup.seq.items {
                    self.visit_expr(item);
                }
            }
            Expr::Return(ret) => {
                if let Some(val) = ret {
                    self.visit_expr(val);
                }
            }
            Expr::For(for_expr) => {
                self.visit_expr(&for_expr.expr);
                // Loop body may execute 0 or more times, so treat like a branch
                let state_before = self.save_state();
                self.visit_expr(&for_expr.body);
                let state_after = self.save_state();
                self.merge_states(&state_before, &state_after);
            }
            Expr::While(while_expr) => {
                self.visit_expr(&while_expr.cond);
                let state_before = self.save_state();
                self.visit_expr(&while_expr.body);
                let state_after = self.save_state();
                self.merge_states(&state_before, &state_after);
            }
            Expr::Loop(loop_expr) => {
                self.visit_expr(&loop_expr.body);
            }
            Expr::Index(index) => {
                self.visit_expr(&index.lhs);
                self.visit_expr(&index.index);
            }
            Expr::Ref(rf) => {
                self.visit_expr(&rf.expr);
            }
            Expr::Deref(deref) => {
                self.visit_expr(&deref.expr);
            }
            Expr::Boxed(boxed) => {
                self.visit_expr(&boxed.inner);
            }
            Expr::New(_) => {
                // new(T) has no sub-expressions to visit
            }
            Expr::Closure(closure) => {
                // Walk closure body with the current context. This is conservative:
                // if the closure consumes a *mut T (e.g., freeze(p)), we treat it
                // as consumed in the enclosing scope. This is safe because the closure
                // may be called before any subsequent use of the variable.
                self.visit_expr(&closure.body);
            }
            Expr::Func(_) => {
                // Nested functions don't get their own DefId, so validate_ownership
                // is never called for them separately. Ideally we'd walk them with a
                // fresh context, but the type checker doesn't support Expr::Func yet
                // (hits todo!("expr::func")), so inferred_local_type would panic.
                // Blocked on type checker support for nested functions.
            }
            Expr::Cast(cast) => {
                self.visit_expr(&cast.lhs);
            }
            Expr::ScopedAccess(sa) => {
                self.visit_expr(&sa.lhs);
            }
            Expr::Curly(curly) => {
                for elem in &curly.elements {
                    match &elem.value {
                        CurlyElement::Labeled(_, val) => {
                            self.visit_expr(val);
                        }
                        CurlyElement::Name(_) => {
                            // Shorthand `{ x }` is desugared to `{ x: x }` during
                            // transformation. Since ownership validation runs on the
                            // transformed AST, this variant is unreachable.
                        }
                    }
                }
            }
            Expr::List(list) => {
                for item in &list.items {
                    self.visit_expr(item);
                }
            }
            // Literals and other leaf expressions — nothing to visit
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefId,
        local_binding::LocalBindingId,
        pathlib::{FilePath, ModulePath},
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            ownership::validate_ownership,
            parse::parse_file,
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn validate_ownership_error_for_use_after_freeze() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // freeze(p) consumes p, then p is used again — error
        let source = r#"
fn bad() {
    p = box(42)
    q = freeze(p)
    p
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

        let errors = validate_ownership(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for use of consumed *mut value"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("consumed")),
            "Error should mention consumed value: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ownership_no_error_for_freeze_without_reuse() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // freeze(p) consumes p, but p is never used again — no error
        let source = r#"
fn ok() {
    p = box(42)
    q = freeze(p)
    q
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

        let errors = validate_ownership(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for freeze without reuse, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Closure capture tests
    // ====================================================================

    #[test]
    fn validate_ownership_closure_consuming_mut_ref_marks_consumed() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Closure calls freeze(p), then p is used after the closure — error
        let source = r#"
fn bad() {
    p = box(42)
    f = () => freeze(p)
    p
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

        let errors = validate_ownership(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for use after closure consumes *mut value"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("consumed")),
            "Error should mention consumed value: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ownership_closure_not_consuming_is_ok() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Closure uses p but doesn't consume it — no error
        let source = r#"
fn ok() {
    p = box(42)
    f = () => p
    p
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

        let errors = validate_ownership(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors when closure doesn't consume, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Nested function tests
    // ====================================================================

    #[test]
    #[ignore = "blocked on type checker support for Expr::Func (nested functions)"]
    fn validate_ownership_nested_fn_freeze_validated() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Nested function has its own use-after-freeze — should still be caught
        let source = r#"
fn outer() {
    fn inner() {
        p = box(42)
        q = freeze(p)
        p
    }
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
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_ownership(&db, outer_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error from nested function's use-after-freeze"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("consumed")),
            "Error should mention consumed value: {:?}",
            errors
        );
    }

    #[test]
    #[ignore = "blocked on type checker support for Expr::Func (nested functions)"]
    fn validate_ownership_nested_fn_does_not_affect_outer_scope() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Outer function has p, nested function is independent — no error
        let source = r#"
fn outer() {
    p = box(42)
    fn inner() {
        q = box(10)
        freeze(q)
    }
    p
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
        let outer_def = parse_result
            .defs
            .iter()
            .find(|d| d.name == "outer")
            .expect("should find outer function");

        let errors = validate_ownership(&db, outer_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors — nested fn doesn't affect outer scope, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Move parameter tests
    // ====================================================================

    #[test]
    fn validate_ownership_move_param_consumes_argument() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // take() has a `move` parameter, so passing p consumes it
        let source = r#"
fn take(move x: *mut int) {
    freeze(x)
}

fn bad() {
    p = box(42)
    take(p)
    p
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

        let errors = validate_ownership(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for use after move parameter consumes value"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("consumed")),
            "Error should mention consumed value: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ownership_non_move_param_does_not_consume() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // borrow() does NOT have a `move` parameter, so p is not consumed
        let source = r#"
fn borrow(x: *mut int) {
    x
}

fn ok() {
    p = box(42)
    borrow(p)
    p
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

        let errors = validate_ownership(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors for non-move parameter, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // Reborrow tests (5a): *mut T available after non-move call
    // ====================================================================

    #[test]
    fn validate_ownership_reborrow_after_non_move_call() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // borrow() takes a non-move *mut int parameter.
        // After borrow(p), p should still be alive (reborrow semantics).
        let source = r#"
fn borrow(x: *mut int) {
    x
}

fn ok() {
    p = box(42)
    borrow(p)
    borrow(p)
    p
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

        let errors = validate_ownership(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors: *mut T should be available after non-move call (reborrow), got: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ownership_move_then_reborrow_is_error() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // take() has a `move` parameter, so p is consumed.
        // The subsequent borrow(p) should be an error.
        let source = r#"
fn take(move x: *mut int) {
    freeze(x)
}

fn borrow(x: *mut int) {
    x
}

fn bad() {
    p = box(42)
    take(p)
    borrow(p)
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

        let errors = validate_ownership(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error: borrow after move should fail"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("consumed")),
            "Error should mention consumed value: {:?}",
            errors
        );
    }

    // ====================================================================
    // Borrow conflict tests (5c): path-level borrowing
    // ====================================================================

    #[test]
    fn validate_ownership_same_var_passed_twice_is_conflict() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Passing the same *mut T variable to two parameters → conflict
        let source = r#"
fn two_args(x: *mut int, y: *mut int) {
    x
}

fn bad() {
    p = box(42)
    two_args(p, p)
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

        let errors = validate_ownership(&db, bad_def.def_id);
        assert!(
            !errors.is_empty(),
            "Expected error for conflicting borrows: same variable passed twice"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("conflicting borrows")),
            "Error should mention conflicting borrows: {:?}",
            errors
        );
    }

    #[test]
    fn validate_ownership_different_vars_no_conflict() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Two different *mut T variables passed to the same call → no conflict
        let source = r#"
fn two_args(x: *mut int, y: *mut int) {
    x
}

fn ok() {
    p = box(42)
    q = box(99)
    two_args(p, q)
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

        let errors = validate_ownership(&db, ok_def.def_id);
        assert!(
            errors.is_empty(),
            "Expected no errors: different variables don't conflict, got: {:?}",
            errors
        );
    }

    // ====================================================================
    // BorrowPath unit tests
    // ====================================================================

    #[test]
    fn borrow_path_same_root_overlaps() {
        use super::BorrowPath;

        let root = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let a = BorrowPath {
            root,
            fields: vec![],
        };
        let b = BorrowPath {
            root,
            fields: vec![],
        };
        assert!(a.overlaps(&b), "Same variable should overlap");
    }

    #[test]
    fn borrow_path_prefix_overlaps() {
        use super::BorrowPath;

        let root = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let parent = BorrowPath {
            root,
            fields: vec![],
        };
        let child = BorrowPath {
            root,
            fields: vec!["x".to_string()],
        };
        assert!(
            parent.overlaps(&child),
            "Parent path overlaps child path (p and p.x)"
        );
        assert!(
            child.overlaps(&parent),
            "Child path overlaps parent path (p.x and p)"
        );
    }

    #[test]
    fn borrow_path_disjoint_fields() {
        use super::BorrowPath;

        let root = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let x = BorrowPath {
            root,
            fields: vec!["x".to_string()],
        };
        let y = BorrowPath {
            root,
            fields: vec!["y".to_string()],
        };
        assert!(
            !x.overlaps(&y),
            "p.x and p.y should NOT overlap (disjoint fields)"
        );
    }

    #[test]
    fn borrow_path_different_roots_no_overlap() {
        use super::BorrowPath;

        let root_a = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let root_b = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 2);
        let a = BorrowPath {
            root: root_a,
            fields: vec!["x".to_string()],
        };
        let b = BorrowPath {
            root: root_b,
            fields: vec!["x".to_string()],
        };
        assert!(
            !a.overlaps(&b),
            "Different roots should not overlap even with same field"
        );
    }

    #[test]
    fn borrow_path_nested_field_overlap() {
        use super::BorrowPath;

        let root = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let shallow = BorrowPath {
            root,
            fields: vec!["x".to_string()],
        };
        let deep = BorrowPath {
            root,
            fields: vec!["x".to_string(), "y".to_string()],
        };
        assert!(
            shallow.overlaps(&deep),
            "p.x and p.x.y should overlap (prefix relationship)"
        );
    }

    #[test]
    fn borrow_path_nested_disjoint() {
        use super::BorrowPath;

        let root = LocalBindingId::new(DefId::new(ray_shared::file_id::FileId(0), 0), 1);
        let a = BorrowPath {
            root,
            fields: vec!["x".to_string(), "a".to_string()],
        };
        let b = BorrowPath {
            root,
            fields: vec!["x".to_string(), "b".to_string()],
        };
        assert!(
            !a.overlaps(&b),
            "p.x.a and p.x.b should NOT overlap (disjoint at second level)"
        );
    }
}
