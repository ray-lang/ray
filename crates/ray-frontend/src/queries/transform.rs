//! AST transformation query for the incremental compiler.
//!
//! The `file_ast` query produces the transformed AST for a file. This is the
//! primary AST representation used by most downstream queries. It applies
//! syntactic and structural transformations that prepare the AST for typechecking.

use std::collections::HashMap;

use ray_core::{
    ast::{
        CurlyElement, Decl, Expr, File, FnParam, FuncSig, Node, Trait,
        transform::{convert_func_to_closure, desugar_compound_assignment, expand_curly_shorthand},
    },
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::DefHeader,
    file_id::FileId,
    node_id::NodeId,
    pathlib::FilePath,
    resolution::Resolution,
    span::{Source, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::TyScheme;

use crate::{
    queries::{parse::parse_file, resolve::name_resolutions},
    query::{Database, Query},
};

/// Result of transforming a source file's AST.
///
/// Contains the transformed AST, source map (updated for synthetic nodes),
/// definition headers, and any transformation errors.
#[derive(Clone)]
pub struct FileAst {
    /// The transformed AST.
    pub ast: File,

    /// Source mapping (inherited from ParseResult, updated for synthetic nodes).
    pub source_map: SourceMap,

    /// Definition headers from parsing (unchanged).
    pub defs: Vec<DefHeader>,

    /// Transformation errors.
    pub errors: Vec<RayError>,
}

/// Produces the transformed AST for a file.
///
/// This query applies several transformations to the raw parsed AST:
/// 1. Compound assignment desugaring: `x += 1` becomes `x = x + 1`
/// 2. Curly shorthand expansion: `Point { x }` becomes `Point { x: x }`
/// 3. Function literal to closure: Anonymous `fn` expressions become closures
///
/// Note: Field ordering and field existence validation are handled during
/// typechecking, not here. This avoids a query cycle between file_ast and
/// struct_def.
///
/// Most downstream queries should depend on `file_ast`, not `parse_file`.
/// Exceptions include `file_imports`, `file_exports`, and `name_resolutions`
/// which operate on the raw parse result.
#[query]
pub fn file_ast(db: &Database, file_id: FileId) -> FileAst {
    let parse_result = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);

    let mut ast = parse_result.ast.clone();
    let mut source_map = parse_result.source_map.clone();
    let mut errors = parse_result.errors.clone();

    // Create a context for transformations
    let mut ctx = TransformContext {
        source_map: &mut source_map,
        errors: &mut errors,
        resolutions: &resolutions,
        filepath: &ast.filepath,
    };

    // Transform declarations
    for decl in &mut ast.decls {
        transform_decl(decl, &mut ctx);
    }

    // Transform top-level statements
    for stmt in &mut ast.stmts {
        transform_expr(stmt, &mut ctx);
    }

    FileAst {
        ast,
        source_map,
        defs: parse_result.defs,
        errors,
    }
}

/// Context for AST transformations.
struct TransformContext<'a> {
    source_map: &'a mut SourceMap,
    errors: &'a mut Vec<RayError>,
    resolutions: &'a HashMap<NodeId, Resolution>,
    filepath: &'a FilePath,
}

/// Transform a declaration node.
fn transform_decl(decl: &mut Node<Decl>, ctx: &mut TransformContext<'_>) {
    match &mut decl.value {
        Decl::Func(func) => {
            if let Some(body) = &mut func.body {
                transform_expr(body, ctx);
            }
        }
        Decl::Impl(im) => {
            // Transform functions in impl blocks
            if let Some(funcs) = &mut im.funcs {
                for func in funcs {
                    if let Some(body) = &mut func.value.body {
                        transform_expr(body, ctx);
                    }
                }
            }
        }
        Decl::Trait(tr) => {
            // Annotate self parameters with the trait's type
            annotate_trait_self_params(tr, ctx.source_map);

            // Transform default method implementations in traits
            for field in &mut tr.fields {
                if let Decl::Func(func) = &mut field.value {
                    if let Some(body) = &mut func.body {
                        transform_expr(body, ctx);
                    }
                }
            }
        }
        Decl::Extern(ext) => {
            // Recurse into the inner declaration
            let inner_decl = ext.decl_mut();
            match inner_decl {
                Decl::Func(func) => {
                    if let Some(body) = &mut func.body {
                        transform_expr(body, ctx);
                    }
                }
                _ => {}
            }
        }
        // Other declaration types don't contain expressions to transform
        Decl::Struct(_)
        | Decl::FnSig(_)
        | Decl::TypeAlias(_, _)
        | Decl::Mutable(_)
        | Decl::Name(_)
        | Decl::Declare(_) => {}
    }
}

/// Transform an expression node recursively.
///
/// This uses the existing AST walker pattern but with mutation.
/// For each expression, we first recurse into children, then apply
/// transformations to the current node.
fn transform_expr(expr: &mut Node<Expr>, ctx: &mut TransformContext<'_>) {
    // First, recursively transform child expressions
    transform_expr_children(expr, ctx);

    // Then apply transformations to this node
    // Capture needed values before the mutable match to avoid borrow conflicts
    let def_id = expr.id.owner;
    let node_id = expr.id;
    let src = ctx.source_map.get(expr);

    match &mut expr.value {
        Expr::Assign(assign) => {
            // Compound assignment desugaring: x += 1 -> x = x + 1
            match desugar_compound_assignment(assign, ctx.source_map) {
                Ok((new_assign, new_srcmap)) => {
                    *assign = new_assign;
                    *ctx.source_map = new_srcmap;
                }
                Err(err) => {
                    ctx.errors.push(err);
                }
            }
        }
        Expr::Curly(curly) => {
            // Curly shorthand expansion: Point { x } -> Point { x: x }
            // Field ordering and field existence validation are handled during
            // typechecking, not here.
            if curly.lhs.is_none() {
                return;
            }

            // Try to resolve the struct type using the node_id's resolution
            let is_resolved = ctx
                .resolutions
                .get(&node_id)
                .is_some_and(|res| matches!(res, Resolution::Def(_)));

            // Emit error if struct type couldn't be resolved
            if !is_resolved {
                if let Some(lhs) = &curly.lhs {
                    ctx.errors.push(RayError {
                        msg: format!("struct type `{}` is undefined", lhs),
                        src: vec![Source {
                            span: lhs.span().copied(),
                            filepath: ctx.filepath.clone(),
                            ..Default::default()
                        }],
                        kind: RayErrorKind::Type,
                        context: Some("struct construction".to_string()),
                    });
                }
            }

            // Always expand shorthand for downstream passes (typechecker expects this)
            expand_curly_shorthand(curly, ctx.source_map, def_id);
        }
        Expr::Func(func) => {
            // Function literal to closure conversion - only for anonymous functions
            if func.sig.is_anon {
                match convert_func_to_closure(func, &src) {
                    Ok(closure) => {
                        expr.value = Expr::Closure(closure);
                    }
                    Err(err) => {
                        ctx.errors.push(err);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Recursively transform child expressions.
fn transform_expr_children(expr: &mut Node<Expr>, ctx: &mut TransformContext<'_>) {
    match &mut expr.value {
        Expr::BinOp(binop) => {
            transform_expr(&mut binop.lhs, ctx);
            transform_expr(&mut binop.rhs, ctx);
        }
        Expr::UnaryOp(unop) => {
            transform_expr(&mut unop.expr, ctx);
        }
        Expr::Call(call) => {
            transform_expr(&mut call.callee, ctx);
            for arg in &mut call.args.items {
                transform_expr(arg, ctx);
            }
        }
        Expr::Index(idx) => {
            transform_expr(&mut idx.lhs, ctx);
            transform_expr(&mut idx.index, ctx);
        }
        Expr::Dot(dot) => {
            transform_expr(&mut dot.lhs, ctx);
        }
        Expr::ScopedAccess(sa) => {
            transform_expr(&mut sa.lhs, ctx);
        }
        Expr::Assign(assign) => {
            transform_expr(&mut assign.rhs, ctx);
        }
        Expr::Block(block) => {
            for stmt in &mut block.stmts {
                transform_expr(stmt, ctx);
            }
        }
        Expr::If(if_expr) => {
            transform_expr(&mut if_expr.cond, ctx);
            transform_expr(&mut if_expr.then, ctx);
            if let Some(else_arm) = &mut if_expr.els {
                transform_expr(else_arm, ctx);
            }
        }
        Expr::For(for_expr) => {
            transform_expr(&mut for_expr.expr, ctx);
            transform_expr(&mut for_expr.body, ctx);
        }
        Expr::While(while_expr) => {
            transform_expr(&mut while_expr.cond, ctx);
            transform_expr(&mut while_expr.body, ctx);
        }
        Expr::Loop(loop_expr) => {
            transform_expr(&mut loop_expr.body, ctx);
        }
        Expr::Tuple(tuple) => {
            for elem in &mut tuple.seq.items {
                transform_expr(elem, ctx);
            }
        }
        Expr::List(list) => {
            for elem in &mut list.items {
                transform_expr(elem, ctx);
            }
        }
        Expr::Set(set) => {
            for elem in &mut set.items {
                transform_expr(elem, ctx);
            }
        }
        Expr::Dict(dict) => {
            for (k, v) in &mut dict.entries {
                transform_expr(k, ctx);
                transform_expr(v, ctx);
            }
        }
        Expr::Range(range) => {
            transform_expr(&mut range.start, ctx);
            transform_expr(&mut range.end, ctx);
        }
        Expr::Curly(curly) => {
            // Transform curly element expressions
            for elem in &mut curly.elements {
                if let CurlyElement::Labeled(_, ref mut e) = elem.value {
                    transform_expr(e, ctx);
                }
            }
        }
        Expr::New(new_expr) => {
            if let Some(count) = &mut new_expr.count {
                transform_expr(count, ctx);
            }
        }
        Expr::Cast(cast) => {
            transform_expr(&mut cast.lhs, ctx);
        }
        Expr::Closure(closure) => {
            transform_expr(&mut closure.body, ctx);
        }
        Expr::Func(func) => {
            if let Some(body) = &mut func.body {
                transform_expr(body, ctx);
            }
        }
        Expr::Return(ret) => {
            if let Some(value) = ret {
                transform_expr(value, ctx);
            }
        }
        Expr::Break(brk) => {
            if let Some(value) = brk {
                transform_expr(value, ctx);
            }
        }
        Expr::Boxed(boxed) => {
            transform_expr(&mut boxed.inner, ctx);
        }
        Expr::Deref(deref) => {
            transform_expr(&mut deref.expr, ctx);
        }
        Expr::Some(some) => {
            transform_expr(some, ctx);
        }
        Expr::Sequence(seq) => {
            for item in &mut seq.items {
                transform_expr(item, ctx);
            }
        }
        Expr::DefaultValue(inner) => {
            transform_expr(inner, ctx);
        }
        Expr::Labeled(_, inner) => {
            transform_expr(inner, ctx);
        }
        Expr::Paren(inner) => {
            transform_expr(inner, ctx);
        }
        Expr::Ref(rf) => {
            transform_expr(&mut rf.expr, ctx);
        }
        Expr::TypeAnnotated(inner, _) => {
            transform_expr(inner, ctx);
        }
        Expr::Unsafe(inner) => {
            transform_expr(inner, ctx);
        }
        // Leaf expressions with no children
        Expr::Name(_)
        | Expr::Literal(_)
        | Expr::Continue
        | Expr::Missing(_)
        | Expr::Path(_)
        | Expr::Pattern(_)
        | Expr::Type(_) => {}
    }
}

/// Annotate trait method self parameters with the trait's type.
///
/// For trait methods, if the first parameter is named `self` without a type
/// annotation, we fill in the trait's self type. This is a syntactic
/// transformation that allows users to write `self` without an explicit type.
fn annotate_trait_self_params(tr: &mut Trait, srcmap: &mut SourceMap) {
    let self_ty = tr.ty.clone_value();

    for field in &mut tr.fields {
        match &mut field.value {
            Decl::FnSig(sig) => {
                annotate_self_param_if_missing(sig, &self_ty, srcmap);
            }
            Decl::Func(func) => {
                annotate_self_param_if_missing(&mut func.sig, &self_ty, srcmap);
            }
            _ => {}
        }
    }
}

/// Annotate a function signature's first parameter with a type if it's named
/// `self` and missing an annotation.
fn annotate_self_param_if_missing(sig: &mut FuncSig, self_ty: &Ty, srcmap: &SourceMap) {
    let Some(first) = sig.params.first_mut() else {
        return;
    };

    // Only annotate if the first param is named `self`
    if !first.value.name().is_self() {
        return;
    }

    // Skip if already annotated
    if first.value.ty().is_some() {
        return;
    }

    // Create a Parsed<TyScheme> with the trait's self type
    let param_span = srcmap.span_of(first);
    let ty_scheme = TyScheme::from_mono(self_ty.clone());
    let parsed_ty = Parsed::new(
        ty_scheme,
        Source {
            span: Some(param_span),
            filepath: FilePath::default(),
            ..Default::default()
        },
    );

    // Apply the annotation
    match &mut first.value {
        FnParam::Name(name) => {
            name.ty = Some(parsed_ty);
        }
        FnParam::Missing { placeholder, .. } => {
            placeholder.ty = Some(parsed_ty);
        }
        FnParam::DefaultValue(_, _) => {
            // Default values on self parameters are not typical, skip
        }
    }
}

#[cfg(test)]
mod tests {
    use ray_core::ast::{CurlyElement, Decl, Expr};
    use ray_shared::pathlib::{FilePath, ModulePath, Path};

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            transform::file_ast,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), std::collections::HashMap::new());
    }

    #[test]
    fn file_ast_returns_transformed_ast() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn main() {}".to_string());

        let result = file_ast(&db, file_id);

        assert!(result.errors.is_empty());
        assert_eq!(result.defs.len(), 1);
        assert_eq!(result.defs[0].name, "main");
    }

    #[test]
    fn file_ast_desugars_compound_assignment() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // x += 1 should become x = x + 1
        FileSource::new(
            &db,
            file_id,
            r#"
fn main() {
    x = 0
    x += 1
}
"#
            .to_string(),
        );

        let result = file_ast(&db, file_id);

        // The transformation should succeed without errors
        assert!(
            result.errors.is_empty(),
            "Expected no errors, got: {:?}",
            result.errors
        );

        // Check that the AST was transformed
        // We can verify by looking at the structure - after desugaring,
        // the RHS of the assignment should be a BinOp
        let func = result
            .ast
            .decls
            .iter()
            .find_map(|d| match &d.value {
                Decl::Func(f) => Some(f),
                _ => None,
            })
            .expect("should have a function");

        let body = func.body.as_ref().expect("function should have body");
        if let Expr::Block(block) = &body.value {
            // Second statement should be the transformed assignment
            if block.stmts.len() >= 2 {
                if let Expr::Assign(assign) = &block.stmts[1].value {
                    // After desugaring, op should be Assign (not AssignOp)
                    assert!(
                        matches!(assign.op, ray_core::ast::InfixOp::Assign),
                        "Expected op to be Assign after desugaring"
                    );
                    // RHS should be a BinOp (x + 1)
                    assert!(
                        matches!(&assign.rhs.value, ray_core::ast::Expr::BinOp(_)),
                        "Expected RHS to be BinOp after desugaring"
                    );
                }
            }
        }
    }

    #[test]
    fn file_ast_expands_curly_shorthand() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Curly shorthand should always be expanded (type checker assumes it)
        FileSource::new(
            &db,
            file_id,
            r#"
struct Point { x: int, y: int }

fn main() {
    x = 1
    y = 2
    p = Point { x, y }
}
"#
            .to_string(),
        );

        let result = file_ast(&db, file_id);

        assert!(
            result.errors.is_empty(),
            "Expected no errors, got: {:?}",
            result.errors
        );

        // Find the curly expression and verify shorthand is expanded
        let func = result
            .ast
            .decls
            .iter()
            .find_map(|d| match &d.value {
                Decl::Func(f) if f.sig.path.name() == Some("main".to_string()) => Some(f),
                _ => None,
            })
            .expect("should have main function");

        let body = func.body.as_ref().expect("function should have body");
        if let Expr::Block(block) = &body.value {
            if let Some(last_stmt) = block.stmts.last() {
                if let Expr::Assign(assign) = &last_stmt.value {
                    if let Expr::Curly(curly) = &assign.rhs.value {
                        // All elements must be Labeled (type checker assumes this)
                        for elem in &curly.elements {
                            assert!(
                                matches!(&elem.value, CurlyElement::Labeled(_, _)),
                                "Expected all curly elements to be Labeled after expansion"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn file_ast_converts_func_literal_to_closure() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Anonymous fn should become a Closure
        FileSource::new(
            &db,
            file_id,
            r#"
fn main() {
    f = fn(x) => x + 1
}
"#
            .to_string(),
        );

        let result = file_ast(&db, file_id);

        // Transformation should succeed
        assert!(
            result.errors.is_empty(),
            "Expected no errors, got: {:?}",
            result.errors
        );

        // Find the function and verify the fn literal was converted
        let func = result
            .ast
            .decls
            .iter()
            .find_map(|d| match &d.value {
                Decl::Func(f) => Some(f),
                _ => None,
            })
            .expect("should have a function");

        let body = func.body.as_ref().expect("function should have body");
        if let Expr::Block(block) = &body.value {
            if let Some(stmt) = block.stmts.first() {
                if let Expr::Assign(assign) = &stmt.value {
                    // RHS should now be a Closure (not Func)
                    assert!(
                        matches!(&assign.rhs.value, ray_core::ast::Expr::Closure(_)),
                        "Expected RHS to be Closure after transformation, got {:?}",
                        assign.rhs.value
                    );
                }
            }
        }
    }

    #[test]
    fn file_ast_preserves_parse_errors() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let file_id = workspace.add_file(FilePath::from("test.ray"), Path::from("test"));
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);
        FileSource::new(&db, file_id, "fn main( {".to_string());

        let result = file_ast(&db, file_id);

        // Parse errors should be preserved
        assert!(!result.errors.is_empty());
    }

    #[test]
    fn file_ast_preserves_curly_field_order() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        // Use proper module path structure for resolution to work
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(
            FilePath::from("test/mod.ray"),
            module_path.clone().to_path(),
        );
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Fields in any order should be preserved (ordering is handled by typechecker)
        FileSource::new(
            &db,
            file_id,
            r#"
struct Point { x: int, y: int }

fn main() {
    p = Point { y: 2, x: 1 }
}
"#
            .to_string(),
        );

        let result = file_ast(&db, file_id);

        // Should have no errors
        assert!(
            result.errors.is_empty(),
            "Expected no errors, got: {:?}",
            result.errors
        );

        // Find the curly expression and verify fields are preserved in source order
        let func = result
            .ast
            .decls
            .iter()
            .find_map(|d| match &d.value {
                Decl::Func(f) if f.sig.path.name() == Some("main".to_string()) => Some(f),
                _ => None,
            })
            .expect("should have main function");

        let body = func.body.as_ref().expect("function should have body");
        if let Expr::Block(block) = &body.value {
            if let Some(stmt) = block.stmts.first() {
                if let Expr::Assign(assign) = &stmt.value {
                    if let Expr::Curly(curly) = &assign.rhs.value {
                        // Fields should be preserved in source order: y, x
                        // (ordering/validation happens in typechecker, not file_ast)
                        assert_eq!(curly.elements.len(), 2, "Should have 2 fields");

                        // Extract field names
                        let field_names: Vec<String> = curly
                            .elements
                            .iter()
                            .filter_map(|elem| match &elem.value {
                                CurlyElement::Labeled(name, _) => name.path.name(),
                                CurlyElement::Name(name) => name.path.name(),
                            })
                            .collect();

                        assert_eq!(
                            field_names,
                            vec!["y".to_string(), "x".to_string()],
                            "Fields should be preserved in source order (y, x)"
                        );
                    }
                }
            }
        }
    }

    // Note: The parser currently requires all trait method parameters to have
    // explicit type annotations, including `self`. If a future parser change
    // allows unannotated self parameters (e.g., `fn eq(self, other: 'a)`),
    // the `annotate_trait_self_params` transformation will automatically
    // fill in the trait's type for the self parameter.

    #[test]
    fn file_ast_preserves_explicit_self_annotation() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Trait method with explicitly annotated self parameter
        FileSource::new(
            &db,
            file_id,
            r#"
trait Eq['a] {
    fn eq(self: 'a, other: 'a) -> bool
}
"#
            .to_string(),
        );

        let result = file_ast(&db, file_id);

        assert!(
            result.errors.is_empty(),
            "Expected no errors, got: {:?}",
            result.errors
        );

        // Find the trait
        let tr = result
            .ast
            .decls
            .iter()
            .find_map(|d| match &d.value {
                Decl::Trait(t) => Some(t),
                _ => None,
            })
            .expect("should have trait");

        // Find the eq method
        let eq_sig = tr
            .fields
            .iter()
            .find_map(|f| match &f.value {
                Decl::FnSig(sig) if sig.path.name() == Some("eq".to_string()) => Some(sig),
                _ => None,
            })
            .expect("should have eq method");

        // First param should still have its original annotation
        let first_param = eq_sig.params.first().expect("should have first param");
        assert!(
            first_param.value.ty().is_some(),
            "Self parameter should have type annotation"
        );
    }

    #[test]
    fn file_ast_error_for_undefined_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Use an undefined struct type
        let source = r#"fn foo() { p = UndefinedStruct { x: 1 } }"#;
        FileSource::new(&db, file_id, source.to_string());

        let result = file_ast(&db, file_id);

        // Should have an error for undefined struct
        assert!(
            !result.errors.is_empty(),
            "Expected error for undefined struct type"
        );
        assert!(
            result
                .errors
                .iter()
                .any(|e| e.msg.contains("undefined") || e.msg.contains("not defined")),
            "Error message should mention undefined: {:?}",
            result.errors
        );
    }

    #[test]
    fn file_ast_no_error_for_defined_struct() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define and use a struct
        let source = r#"
struct Point { x: int, y: int }
fn foo() { p = Point { x: 1, y: 2 } }
"#;
        FileSource::new(&db, file_id, source.to_string());

        let result = file_ast(&db, file_id);

        // Should have no struct-related errors
        let struct_errors: Vec<_> = result
            .errors
            .iter()
            .filter(|e| e.msg.contains("struct") || e.msg.contains("undefined"))
            .collect();
        assert!(
            struct_errors.is_empty(),
            "Expected no struct-related errors, got: {:?}",
            struct_errors
        );
    }
}
