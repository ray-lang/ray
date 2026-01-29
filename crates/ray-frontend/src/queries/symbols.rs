use std::collections::{HashMap, HashSet};

use ray_core::ast::{Decl, Expr, WalkItem, walk_file};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    resolution::{DefTarget, Resolution},
    symbol::{SymbolIdentity, SymbolRole, SymbolTarget},
};

use crate::{
    queries::{
        calls::call_resolution,
        parse::parse_file,
        resolve::name_resolutions,
    },
    query::{Database, Query},
};

/// Resolve a NodeId to symbol targets.
///
/// Returns the resolved identity of the symbol at the NodeId. If the NodeId
/// is a definition site, returns a `Definition` role. Otherwise, returns the
/// resolved identity as a `Reference`.
///
/// For method calls, this includes the impl target and (if applicable) the trait
/// method target.
///
/// **Dependencies**: `definition_identities(file_id)`, `name_resolutions(file_id)`,
/// `call_site_index(file_id)`, `call_resolution(NodeId)`
#[query]
pub fn symbol_targets(db: &Database, node_id: NodeId) -> Vec<SymbolTarget> {
    let file_id = node_id.owner.file;
    let definition_identities = definition_identities(db, file_id);
    if let Some(identity) = definition_identities.get(&node_id) {
        return vec![SymbolTarget::new(identity.clone(), SymbolRole::Definition)];
    }

    let resolutions = name_resolutions(db, file_id);
    if let Some(resolution) = resolutions.get(&node_id) {
        return symbol_targets_from_resolution(resolution, SymbolRole::Reference);
    }

    let call_sites = call_site_index(db, file_id);
    let Some(call_id) = call_sites.get(&node_id).copied() else {
        return Vec::new();
    };

    let Some(resolution) = call_resolution(db, call_id) else {
        return Vec::new();
    };

    let mut targets = Vec::new();
    let mut seen = HashSet::new();

    if let Some(trait_target) = resolution.trait_target {
        let identity = SymbolIdentity::Def(trait_target);
        if seen.insert(identity.clone()) {
            targets.push(SymbolTarget::new(identity, SymbolRole::Reference));
        }
    }

    if let Some(impl_target) = resolution.impl_target {
        let identity = SymbolIdentity::Def(impl_target);
        if seen.insert(identity.clone()) {
            targets.push(SymbolTarget::new(identity, SymbolRole::Reference));
        }
    }

    targets
}

fn symbol_targets_from_resolution(
    resolution: &Resolution,
    role: SymbolRole,
) -> Vec<SymbolTarget> {
    match resolution {
        Resolution::Def(target) => {
            vec![SymbolTarget::new(SymbolIdentity::Def(target.clone()), role)]
        }
        Resolution::Local(local_id) => {
            vec![SymbolTarget::new(SymbolIdentity::Local(*local_id), role)]
        }
        Resolution::TypeParam(_) | Resolution::Error { .. } => Vec::new(),
    }
}

/// Returns definition-site NodeIds and their identities for a file.
///
/// This includes:
/// - Function/trait/struct/type alias names
/// - Top-level binding declarations
/// - Function parameters and local binding definitions (patterns)
///
/// **Dependencies**: `parse_file(file_id)`, `name_resolutions(file_id)`
#[query]
pub fn definition_identities(db: &Database, file_id: FileId) -> HashMap<NodeId, SymbolIdentity> {
    let parse_result = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);
    let mut identities = HashMap::new();

    for item in walk_file(&parse_result.ast) {
        match item {
            WalkItem::Decl(decl) => {
                let def_identity = SymbolIdentity::Def(DefTarget::Workspace(decl.id.owner));
                match &decl.value {
                    Decl::Func(func) => {
                        identities.insert(func.sig.path.id, def_identity);
                        record_fn_params(&func.sig, &resolutions, &mut identities);
                    }
                    Decl::FnSig(sig) => {
                        identities.insert(sig.path.id, def_identity);
                        record_fn_params(sig, &resolutions, &mut identities);
                    }
                    Decl::Struct(st) => {
                        identities.insert(st.path.id, def_identity);
                    }
                    Decl::Trait(tr) => {
                        identities.insert(tr.path.id, def_identity);
                    }
                    Decl::TypeAlias(name, _) => {
                        identities.insert(name.id, def_identity);
                    }
                    Decl::Mutable(name) | Decl::Name(name) => {
                        identities.insert(name.id, def_identity);
                    }
                    Decl::Extern(_) | Decl::Impl(_) | Decl::Declare(_) | Decl::FileMain(_) => {}
                }
            }
            WalkItem::Pattern(pattern) => {
                for node in pattern.paths().into_iter() {
                    let (_path, is_lvalue) = node.value;
                    if is_lvalue {
                        continue;
                    }
                    if let Some(Resolution::Local(local_id)) = resolutions.get(&node.id) {
                        identities.insert(node.id, SymbolIdentity::Local(*local_id));
                    }
                }
            }
            WalkItem::Expr(expr) => {
                if let Expr::Closure(closure) = &expr.value {
                    for arg in &closure.args.items {
                        if let Some(Resolution::Local(local_id)) = resolutions.get(&arg.id) {
                            identities.insert(arg.id, SymbolIdentity::Local(*local_id));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    identities
}

fn record_fn_params(
    sig: &ray_core::ast::FuncSig,
    resolutions: &HashMap<NodeId, Resolution>,
    identities: &mut HashMap<NodeId, SymbolIdentity>,
) {
    for param in &sig.params {
        let param_id = param.id;
        let Some(Resolution::Local(local_id)) = resolutions.get(&param_id) else {
            continue;
        };
        identities.insert(param_id, SymbolIdentity::Local(*local_id));
    }
}

/// Index mapping callee name node IDs to their call expression IDs.
///
/// **Dependencies**: `parse_file(file_id)`
#[query]
pub fn call_site_index(db: &Database, file_id: FileId) -> HashMap<NodeId, NodeId> {
    let parse_result = parse_file(db, file_id);
    let mut index = HashMap::new();

    for item in walk_file(&parse_result.ast) {
        let WalkItem::Expr(expr) = item else {
            continue;
        };

        let Expr::Call(call) = &expr.value else {
            continue;
        };

        match &call.callee.value {
            Expr::Dot(dot) => {
                index.insert(dot.rhs.id, expr.id);
            }
            Expr::ScopedAccess(scoped_access) => {
                index.insert(scoped_access.rhs.id, expr.id);
            }
            _ => {}
        }
    }

    index
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        pathlib::{FilePath, ModulePath},
        resolution::DefTarget,
        resolution::Resolution,
        symbol::{SymbolIdentity, SymbolRole},
    };

    use crate::{
        queries::{
            calls::call_resolution,
            libraries::LoadedLibraries,
            parse::parse_file,
            resolve::name_resolutions,
            symbols::symbol_targets,
            workspace::{FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };
    use ray_core::ast::{Decl, Expr, WalkItem, walk_file};

    fn setup_test_db(source: &str) -> (Database, ray_shared::file_id::FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        FileSource::new(&db, file_id, source.to_string());
        (db, file_id)
    }

    fn setup_test_db_with_libs(source: &str) -> (Database, ray_shared::file_id::FileId) {
        let (db, file_id) = setup_test_db(source);
        LoadedLibraries::new(&db, (), HashMap::new());
        (db, file_id)
    }

    #[test]
    fn symbol_targets_resolves_def_reference() {
        let source = r#"
fn helper() -> int => 1
fn main() -> int => helper()
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let helper_def = parse_result
            .defs
            .iter()
            .find(|def| def.name == "helper")
            .expect("expected helper def");

        let resolutions = name_resolutions(&db, file_id);
        let helper_ref_id = resolutions.iter().find_map(|(node_id, res)| match res {
            Resolution::Def(DefTarget::Workspace(def_id)) if *def_id == helper_def.def_id => {
                Some(*node_id)
            }
            _ => None,
        });

        let helper_ref_id = helper_ref_id.expect("expected helper reference node");
        let targets = symbol_targets(&db, helper_ref_id);

        assert_eq!(targets.len(), 1, "expected one target");
        let target = &targets[0];
        assert!(
            matches!(target.identity, SymbolIdentity::Def(DefTarget::Workspace(def_id)) if def_id == helper_def.def_id),
            "expected helper def target"
        );
        assert_eq!(target.role, SymbolRole::Reference);
    }

    #[test]
    fn symbol_targets_resolves_local_binding_reference() {
        use super::definition_identities;

        let source = r#"
fn main() -> int {
    x = 1
    x
}
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let resolutions = name_resolutions(&db, file_id);
        let def_identities = definition_identities(&db, file_id);

        // Find a local resolution that is NOT a definition site (i.e., a reference)
        let local_ref_id = resolutions.iter().find_map(|(node_id, res)| {
            // Skip if this node is a definition site
            if def_identities.contains_key(node_id) {
                return None;
            }
            match res {
                Resolution::Local(local_id) => Some((*node_id, *local_id)),
                _ => None,
            }
        });

        let (local_ref_id, local_id) = local_ref_id.expect("expected local reference node");
        let targets = symbol_targets(&db, local_ref_id);

        assert_eq!(targets.len(), 1, "expected one target");
        let target = &targets[0];
        assert!(
            matches!(target.identity, SymbolIdentity::Local(id) if id == local_id),
            "expected local binding target"
        );
        assert_eq!(target.role, SymbolRole::Reference);
    }

    #[test]
    fn symbol_targets_resolves_method_call() {
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
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let method_def = parse_result
            .defs
            .iter()
            .find(|def| def.name == "magnitude")
            .expect("expected method def");

        let mut method_name_id = None;
        for item in walk_file(&parse_result.ast) {
            let WalkItem::Expr(expr) = item else {
                continue;
            };
            let Expr::Call(call) = &expr.value else {
                continue;
            };
            if let Expr::Dot(dot) = &call.callee.value {
                if dot.rhs.path.name().as_deref() == Some("magnitude") {
                    method_name_id = Some(dot.rhs.id);
                    break;
                }
            }
        }

        let method_name_id = method_name_id.expect("expected method call name node");
        let targets = symbol_targets(&db, method_name_id);

        // call_resolution expects call expr ID, not method name ID
        assert!(
            call_resolution(&db, method_name_id).is_none(),
            "call_resolution requires call expr ID, not method name ID"
        );
        assert!(
            targets.iter().any(|target| {
                matches!(
                    target.identity,
                    SymbolIdentity::Def(DefTarget::Workspace(def_id))
                        if def_id == method_def.def_id
                )
            }),
            "expected method def target"
        );
        assert!(
            targets.iter().all(|target| target.role == SymbolRole::Reference),
            "expected reference roles for method call"
        );
    }

    #[test]
    fn symbol_targets_marks_definition_node() {
        let source = r#"
fn helper() -> int => 1
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let helper_def = parse_result
            .defs
            .iter()
            .find(|def| def.name == "helper")
            .expect("expected helper def");

        let mut def_name_id = None;
        for decl in &parse_result.ast.decls {
            let Decl::Func(func) = &decl.value else {
                continue;
            };
            if func.sig.path.to_short_name() == "helper" {
                def_name_id = Some(func.sig.path.id);
                break;
            }
        }

        let def_name_id = def_name_id.expect("expected helper def name node");
        let targets = symbol_targets(&db, def_name_id);

        assert_eq!(targets.len(), 1, "expected one target");
        let target = &targets[0];
        assert!(
            matches!(target.identity, SymbolIdentity::Def(DefTarget::Workspace(def_id)) if def_id == helper_def.def_id),
            "expected helper def target"
        );
        assert_eq!(target.role, SymbolRole::Definition);
    }

    #[test]
    #[ignore = "call_resolution doesn't yet populate trait_target for trait method calls"]
    fn symbol_targets_returns_both_trait_and_impl_targets() {
        let source = r#"
trait Greet['t] {
    fn greet(self: *'t) -> int
}

struct Person {}

impl Greet[Person] {
    fn greet(self: *Person) -> int => 1
}

fn test() -> int {
    p = Person {}
    p.greet()
}
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);

        // Find the trait method def and impl method def
        let trait_method_def = parse_result
            .defs
            .iter()
            .find(|def| def.name == "greet" && def.parent.is_some())
            .expect("expected trait method def");

        let mut method_name_id = None;
        for item in walk_file(&parse_result.ast) {
            let WalkItem::Expr(expr) = item else {
                continue;
            };
            let Expr::Call(call) = &expr.value else {
                continue;
            };
            if let Expr::Dot(dot) = &call.callee.value {
                if dot.rhs.path.name().as_deref() == Some("greet") {
                    method_name_id = Some(dot.rhs.id);
                    break;
                }
            }
        }

        let method_name_id = method_name_id.expect("expected method call name node");
        let targets = symbol_targets(&db, method_name_id);

        // Should have both trait method and impl method targets
        assert!(
            targets.len() >= 2,
            "expected both trait and impl targets, got {:?}",
            targets
        );
        assert!(
            targets.iter().any(|t| {
                matches!(&t.identity, SymbolIdentity::Def(DefTarget::Workspace(def_id))
                    if *def_id == trait_method_def.def_id)
            }),
            "expected trait method target"
        );
    }

    #[test]
    fn symbol_targets_marks_function_parameter_as_definition() {
        let source = r#"
fn add(x: int, y: int) -> int => x + y
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let resolutions = name_resolutions(&db, file_id);

        let mut param_node_id = None;
        for decl in &parse_result.ast.decls {
            let Decl::Func(func) = &decl.value else {
                continue;
            };
            if func.sig.path.to_short_name() == "add" {
                if let Some(first_param) = func.sig.params.first() {
                    param_node_id = Some(first_param.id);
                    break;
                }
            }
        }

        let param_node_id = param_node_id.expect("expected parameter node");
        let targets = symbol_targets(&db, param_node_id);

        assert_eq!(targets.len(), 1, "expected one target for parameter");
        let target = &targets[0];

        let expected_local_id = match resolutions.get(&param_node_id) {
            Some(Resolution::Local(id)) => *id,
            _ => panic!("expected local resolution for parameter"),
        };
        assert!(
            matches!(target.identity, SymbolIdentity::Local(id) if id == expected_local_id),
            "expected local identity for parameter"
        );
        assert_eq!(target.role, SymbolRole::Definition);
    }

    #[test]
    fn symbol_targets_marks_closure_argument_as_definition() {
        let source = r#"
fn main() -> int {
    f = (x: int) => x + 1
    f(1)
}
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let resolutions = name_resolutions(&db, file_id);

        // Find closure in AST - closures parsed as Expr::Closure
        let mut closure_arg_id = None;
        for item in walk_file(&parse_result.ast) {
            let WalkItem::Expr(expr) = item else {
                continue;
            };
            // Match on Expr::Closure directly (destructuring with closure binding)
            let Expr::Closure(closure) = &expr.value else {
                continue;
            };
            if let Some(first_arg) = closure.args.items.first() {
                closure_arg_id = Some(first_arg.id);
                break;
            }
        }

        let closure_arg_id = closure_arg_id.expect("expected closure argument node");
        let targets = symbol_targets(&db, closure_arg_id);

        assert_eq!(targets.len(), 1, "expected one target for closure argument");
        let target = &targets[0];

        let expected_local_id = match resolutions.get(&closure_arg_id) {
            Some(Resolution::Local(id)) => *id,
            _ => panic!("expected local resolution for closure argument"),
        };
        assert!(
            matches!(target.identity, SymbolIdentity::Local(id) if id == expected_local_id),
            "expected local identity for closure argument"
        );
        assert_eq!(target.role, SymbolRole::Definition);
    }

    #[test]
    #[ignore = "typing.rs ScopedAccess lowering looks in ctx.resolutions instead of doing type-based member lookup"]
    fn symbol_targets_resolves_scoped_access_call() {
        let source = r#"
struct Math['t] {}

impl object Math['t] {
    static fn double(x: int) -> int => x * 2
}

fn test() -> int => Math[int]::double(5)
"#;
        let (db, file_id) = setup_test_db_with_libs(source);

        let parse_result = parse_file(&db, file_id);
        let method_def = parse_result
            .defs
            .iter()
            .find(|def| def.name == "double")
            .expect("expected double def");

        let mut method_name_id = None;
        for item in walk_file(&parse_result.ast) {
            let WalkItem::Expr(expr) = item else {
                continue;
            };
            let Expr::Call(call) = &expr.value else {
                continue;
            };
            if let Expr::ScopedAccess(scoped) = &call.callee.value {
                if scoped.rhs.path.name().as_deref() == Some("double") {
                    method_name_id = Some(scoped.rhs.id);
                    break;
                }
            }
        }

        let method_name_id = method_name_id.expect("expected scoped access call name node");
        let targets = symbol_targets(&db, method_name_id);

        assert!(
            targets.iter().any(|target| {
                matches!(
                    target.identity,
                    SymbolIdentity::Def(DefTarget::Workspace(def_id))
                        if def_id == method_def.def_id
                )
            }),
            "expected method def target for scoped access call"
        );
        assert!(
            targets.iter().all(|target| target.role == SymbolRole::Reference),
            "expected reference roles"
        );
    }

    // Note: Pattern binding test for destructuring (e.g., `Point { x, y } = ...`)
    // is omitted because destructuring patterns are not yet fully supported.
    // See typing system comment: "destructuring patterns are left for future work."
    // Local binding definitions are tested via function parameters and closure arguments.
}
