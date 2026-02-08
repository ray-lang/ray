//! Operator lookup queries for the incremental compiler.
//!
//! Operators in Ray are methods with symbolic names (e.g., `+`, `-`, `*`).
//! A trait defines an operator by declaring a method with that symbol as its name.

use std::collections::HashMap;

use ray_core::ast::{InfixOp, PrefixOp};
use ray_query_macros::query;
use ray_shared::{resolution::DefTarget, ty::Ty};
use ray_typing::types::TyScheme;

use crate::{
    queries::{
        defs::{trait_def, traits_in_module},
        libraries::{LoadedLibraries, OperatorArity, OperatorEntry, OperatorIndex},
        workspace::WorkspaceSnapshot,
    },
    query::{Database, Query},
};

/// Check if a method name is a valid Ray operator.
///
/// Uses the language's canonical operator definitions from `InfixOp::is()` and `PrefixOp::is()`.
/// Valid operators include: `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `>`, `<=`, `>=`,
/// `&&`, `||`, `&`, `|`, `^`, `<<`, `>>`, `**`, `!`, `~`, `<-`
pub fn is_operator_name(name: &str) -> bool {
    InfixOp::is(name) || PrefixOp::is(name)
}

/// Infer the arity of an operator from the method's type scheme.
///
/// Arity is determined by the number of parameters in the function type:
/// - 1 parameter (just receiver): Prefix (unary operator like `!x`)
/// - 2 parameters (receiver + arg): Infix (binary operator like `a + b`)
///
/// Falls back to Infix for methods with unexpected parameter counts.
fn infer_arity(scheme: &TyScheme) -> OperatorArity {
    match scheme.mono() {
        Ty::Func(params, _) => {
            if params.len() == 1 {
                OperatorArity::Prefix
            } else {
                // 2 or more parameters = infix (binary)
                OperatorArity::Infix
            }
        }
        // If not a function type, default to infix
        _ => OperatorArity::Infix,
    }
}

/// Build an index of all operators from workspace and library traits.
///
/// Scans all traits in the workspace AND loaded libraries for methods with
/// symbolic (non-alphanumeric) names. Builds a map from operator symbol to
/// the trait and method that define it.
///
/// Most operators (like `+`, `-`, `*`) are defined in the core library.
#[query]
pub fn operator_index(db: &Database) -> OperatorIndex {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    let mut index: HashMap<(String, OperatorArity), OperatorEntry> = HashMap::new();

    // Scan workspace traits
    for module_path in workspace.all_module_paths() {
        let trait_ids = traits_in_module(db, module_path.clone());

        for trait_id in trait_ids {
            let trait_target = DefTarget::Workspace(trait_id);
            if let Some(trait_definition) = trait_def(db, trait_target.clone()) {
                for method in &trait_definition.methods {
                    if is_operator_name(&method.name) {
                        let arity = infer_arity(&method.scheme);
                        let entry = OperatorEntry {
                            trait_def: trait_target.clone(),
                            method_def: method.target.clone(),
                            arity,
                        };

                        // Key by (symbol, arity) so that both infix `-` (Sub)
                        // and prefix `-` (Neg) can coexist.
                        index.entry((method.name.clone(), arity)).or_insert(entry);
                    }
                }
            }
        }
    }

    // Include library operators
    let libraries = db.get_input::<LoadedLibraries>(());
    for (_lib_path, lib_data) in &libraries.libraries {
        for ((symbol, arity), entry) in &lib_data.operators {
            // Library operators don't override workspace operators
            index
                .entry((symbol.clone(), *arity))
                .or_insert_with(|| entry.clone());
        }
    }

    index
}

/// Look up an infix (binary) operator by symbol.
///
/// Returns the operator entry if found and the operator has infix arity.
/// Returns `None` if the operator doesn't exist or is a prefix operator.
#[query]
pub fn lookup_infix_op(db: &Database, symbol: String) -> Option<OperatorEntry> {
    let index = operator_index(db);
    index.get(&(symbol, OperatorArity::Infix)).cloned()
}

/// Look up a prefix (unary) operator by symbol.
///
/// Returns the operator entry if found and the operator has prefix arity.
/// Returns `None` if the operator doesn't exist or is an infix operator.
#[query]
pub fn lookup_prefix_op(db: &Database, symbol: String) -> Option<OperatorEntry> {
    let index = operator_index(db);
    index.get(&(symbol, OperatorArity::Prefix)).cloned()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::LibraryDefId,
        pathlib::{FilePath, ModulePath},
        resolution::DefTarget,
    };

    use crate::queries::{
        libraries::{LibraryData, LoadedLibraries, OperatorArity, OperatorEntry},
        operators::{is_operator_name, lookup_infix_op, lookup_prefix_op, operator_index},
        workspace::{FileSource, WorkspaceSnapshot},
    };
    use crate::query::Database;

    /// Helper to set up empty LoadedLibraries in the database.
    fn setup_empty_libraries(db: &Database) {
        LoadedLibraries::new(db, (), HashMap::new(), HashMap::new());
    }

    #[test]
    fn is_operator_name_recognizes_symbols() {
        assert!(is_operator_name("+"));
        assert!(is_operator_name("-"));
        assert!(is_operator_name("*"));
        assert!(is_operator_name("/"));
        assert!(is_operator_name("=="));
        assert!(is_operator_name("!="));
        assert!(is_operator_name("<"));
        assert!(is_operator_name(">"));
        assert!(is_operator_name("<="));
        assert!(is_operator_name(">="));
        assert!(is_operator_name("&&"));
        assert!(is_operator_name("||"));
        assert!(is_operator_name("!"));
        assert!(is_operator_name("<<"));
        assert!(is_operator_name(">>"));
    }

    #[test]
    fn is_operator_name_rejects_alphanumeric() {
        assert!(!is_operator_name("add"));
        assert!(!is_operator_name("plus"));
        assert!(!is_operator_name("eq"));
        assert!(!is_operator_name("cmp"));
        assert!(!is_operator_name("to_string"));
        assert!(!is_operator_name("get_value"));
    }

    #[test]
    fn is_operator_name_rejects_mixed() {
        assert!(!is_operator_name("+add"));
        assert!(!is_operator_name("add+"));
        assert!(!is_operator_name("a+b"));
        assert!(!is_operator_name("_+"));
        assert!(!is_operator_name("+_"));
    }

    #[test]
    fn is_operator_name_rejects_empty_and_whitespace() {
        assert!(!is_operator_name(""));
        assert!(!is_operator_name(" "));
        assert!(!is_operator_name("+ "));
        assert!(!is_operator_name(" +"));
    }

    #[test]
    fn operator_index_finds_workspace_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define a trait with an operator method
        let source = r#"
trait Add['a] {
    fn +(self: 'a, other: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(
            index.contains_key(&("+".to_string(), OperatorArity::Infix)),
            "Should find + operator"
        );
        let entry = index.get(&("+".to_string(), OperatorArity::Infix)).unwrap();
        assert!(
            matches!(entry.trait_def, DefTarget::Workspace(_)),
            "Should be from workspace"
        );
        assert_eq!(entry.arity, OperatorArity::Infix);
    }

    #[test]
    fn operator_index_finds_multiple_operators() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define traits with multiple operators
        let source = r#"
trait Add['a] {
    fn +(self: 'a, other: 'a) -> 'a
}

trait Sub['a] {
    fn -(self: 'a, other: 'a) -> 'a
}

trait Mul['a] {
    fn *(self: 'a, other: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(
            index.contains_key(&("+".to_string(), OperatorArity::Infix)),
            "Should find + operator"
        );
        assert!(
            index.contains_key(&("-".to_string(), OperatorArity::Infix)),
            "Should find - operator"
        );
        assert!(
            index.contains_key(&("*".to_string(), OperatorArity::Infix)),
            "Should find * operator"
        );
    }

    #[test]
    fn operator_index_finds_comparison_operators() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define traits with comparison operators
        let source = r#"
trait Eq['a] {
    fn ==(self: 'a, other: 'a) -> bool
    fn !=(self: 'a, other: 'a) -> bool
}

trait Ord['a] {
    fn <(self: 'a, other: 'a) -> bool
    fn >(self: 'a, other: 'a) -> bool
    fn <=(self: 'a, other: 'a) -> bool
    fn >=(self: 'a, other: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(
            index.contains_key(&("==".to_string(), OperatorArity::Infix)),
            "Should find == operator"
        );
        assert!(
            index.contains_key(&("!=".to_string(), OperatorArity::Infix)),
            "Should find != operator"
        );
        assert!(
            index.contains_key(&("<".to_string(), OperatorArity::Infix)),
            "Should find < operator"
        );
        assert!(
            index.contains_key(&(">".to_string(), OperatorArity::Infix)),
            "Should find > operator"
        );
        assert!(
            index.contains_key(&("<=".to_string(), OperatorArity::Infix)),
            "Should find <= operator"
        );
        assert!(
            index.contains_key(&(">=".to_string(), OperatorArity::Infix)),
            "Should find >= operator"
        );
    }

    #[test]
    fn operator_index_ignores_non_operator_methods() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define a trait with regular methods (not operators)
        let source = r#"
trait Display['a] {
    fn to_string(self: 'a) -> string
    fn format(self: 'a, fmt: string) -> string
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(
            !index.contains_key(&("to_string".to_string(), OperatorArity::Prefix)),
            "Should not treat to_string as operator"
        );
        assert!(
            !index.contains_key(&("format".to_string(), OperatorArity::Prefix)),
            "Should not treat format as operator"
        );
        assert!(index.is_empty(), "Index should be empty");
    }

    #[test]
    fn operator_index_empty_workspace() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let index = operator_index(&db);

        assert!(index.is_empty());
    }

    #[test]
    fn operator_index_includes_library_operators() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with operators
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::ops"));

        // Add an operator to the library
        let add_trait_id = LibraryDefId {
            module: ModulePath::from("core::ops"),
            index: 0,
        };
        let add_method_id = LibraryDefId {
            module: ModulePath::from("core::ops"),
            index: 1,
        };

        core_lib.operators.insert(
            ("+".to_string(), OperatorArity::Infix),
            OperatorEntry {
                trait_def: DefTarget::Library(add_trait_id),
                method_def: DefTarget::Library(add_method_id),
                arity: OperatorArity::Infix,
            },
        );

        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        let index = operator_index(&db);

        assert!(
            index.contains_key(&("+".to_string(), OperatorArity::Infix)),
            "Should find library + operator"
        );
        let entry = index.get(&("+".to_string(), OperatorArity::Infix)).unwrap();
        assert!(
            matches!(entry.trait_def, DefTarget::Library(_)),
            "Should be from library"
        );
    }

    #[test]
    fn operator_index_workspace_overrides_library() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set up a library with the same operator
        let mut libraries = LoadedLibraries::default();
        let mut core_lib = LibraryData::default();
        core_lib.modules.push(ModulePath::from("core::ops"));

        let lib_trait_id = LibraryDefId {
            module: ModulePath::from("core::ops"),
            index: 0,
        };
        let lib_method_id = LibraryDefId {
            module: ModulePath::from("core::ops"),
            index: 1,
        };

        core_lib.operators.insert(
            ("+".to_string(), OperatorArity::Infix),
            OperatorEntry {
                trait_def: DefTarget::Library(lib_trait_id),
                method_def: DefTarget::Library(lib_method_id),
                arity: OperatorArity::Infix,
            },
        );

        libraries.add(ModulePath::from("core"), core_lib);
        db.set_input::<LoadedLibraries>((), libraries);

        // Define a workspace trait with the same operator
        let source = r#"
trait Add['a] {
    fn +(self: 'a, other: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(index.contains_key(&("+".to_string(), OperatorArity::Infix)));
        let entry = index.get(&("+".to_string(), OperatorArity::Infix)).unwrap();
        // Workspace operator should take precedence
        assert!(
            matches!(entry.trait_def, DefTarget::Workspace(_)),
            "Workspace operator should override library operator"
        );
    }

    #[test]
    fn operator_index_prefix_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        // Define a trait with a prefix operator (logical not)
        let source = r#"
trait Not['a] {
    fn !(self: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let index = operator_index(&db);

        assert!(
            index.contains_key(&("!".to_string(), OperatorArity::Prefix)),
            "Should find ! operator"
        );
        let entry = index
            .get(&("!".to_string(), OperatorArity::Prefix))
            .unwrap();
        assert_eq!(entry.arity, OperatorArity::Prefix);
    }

    #[test]
    fn lookup_infix_op_finds_binary_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Add['a] {
    fn +(self: 'a, other: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let entry = lookup_infix_op(&db, "+".to_string());
        assert!(entry.is_some(), "Should find + as infix operator");
        assert_eq!(entry.unwrap().arity, OperatorArity::Infix);
    }

    #[test]
    fn lookup_infix_op_rejects_prefix_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Not['a] {
    fn !(self: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let entry = lookup_infix_op(&db, "!".to_string());
        assert!(entry.is_none(), "Should not find ! as infix operator");
    }

    #[test]
    fn lookup_prefix_op_finds_unary_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Not['a] {
    fn !(self: 'a) -> bool
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let entry = lookup_prefix_op(&db, "!".to_string());
        assert!(entry.is_some(), "Should find ! as prefix operator");
        assert_eq!(entry.unwrap().arity, OperatorArity::Prefix);
    }

    #[test]
    fn lookup_prefix_op_rejects_infix_operator() {
        let db = Database::new();

        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("mymodule");
        let file_id = workspace.add_file(FilePath::from("mymodule/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        let source = r#"
trait Add['a] {
    fn +(self: 'a, other: 'a) -> 'a
}
"#;
        FileSource::new(&db, file_id, source.to_string());

        let entry = lookup_prefix_op(&db, "+".to_string());
        assert!(entry.is_none(), "Should not find + as prefix operator");
    }

    #[test]
    fn lookup_op_returns_none_for_unknown() {
        let db = Database::new();

        let workspace = WorkspaceSnapshot::new();
        db.set_input::<WorkspaceSnapshot>((), workspace);
        setup_empty_libraries(&db);

        assert!(lookup_infix_op(&db, "+".to_string()).is_none());
        assert!(lookup_prefix_op(&db, "!".to_string()).is_none());
    }
}
