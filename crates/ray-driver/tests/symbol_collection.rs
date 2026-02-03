#![cfg(test)]

mod utils;

use std::collections::HashMap;

use ray_codegen::modules::ModuleBuilder;
use ray_core::ast::{CurlyElement, Expr};
use ray_driver::{BuildOptions, Driver};
use ray_frontend::queries::{defs::def_path, symbols::symbol_targets};
use ray_shared::{
    pathlib::{Path, RayPaths},
    symbol::{SymbolIdentity, SymbolRole},
    ty::Ty,
};

use utils::{find_func, find_func_in, find_impl, test_build, test_build_with_options, TestBuildOptions};

#[test]
fn collects_function_and_parameter_definitions() {
    let src = r#"
fn foo(a: int, b: int) -> int {
    42
}
"#;

    let result = match test_build(&src) {
        Ok(result) => result,
        Err(errs) => {
            panic!("Found errors: {:#?}", errs);
        }
    };

    let foo_path = Path::from("test::foo");
    let foo_decl = find_func(&result.db, &foo_path);

    // Use symbol_targets query to get symbol information
    let targets = symbol_targets(&result.db, foo_decl.sig.path.id);
    let sym = targets.first().expect("could not find foo symbol");

    // Verify it's a definition with the correct path
    assert_eq!(sym.role, SymbolRole::Definition);
    if let SymbolIdentity::Def(target) = &sym.identity {
        let path = def_path(&result.db, target.clone())
            .map(|ip| ip.to_path())
            .expect("could not get path for foo definition");
        assert_eq!(path, foo_path);
    } else {
        panic!("expected Def identity, got {:?}", sym.identity);
    }
}

#[test]
fn collects_impl_function() {
    let src = r#"
trait Foo['a] {
    fn foo(self: 'a) -> int
}

impl Foo[int] {
    fn foo(self: int) -> int {
        42
    }
}
"#;
    let result = match test_build(src) {
        Ok(result) => result,
        Err(errs) => {
            panic!("Found errors: {:#?}", errs);
        }
    };

    // Use the qualified trait path with name resolution
    let trait_foo_path = Path::from("test::Foo");
    let impl_ty = Ty::int();
    let impl_foo = find_impl(&result.db, &trait_foo_path, &impl_ty);
    let funcs = impl_foo.funcs.as_ref().expect("impl has no functions");
    // The AST method path uses the implementing type (int), not the trait name
    let func_ast_path = Path::from("test::int::foo");
    let func = find_func_in(funcs, &func_ast_path);

    // Use symbol_targets query to get symbol information
    let targets = symbol_targets(&result.db, func.sig.path.id);
    let sym = targets.first().expect("could not find symbol for int::foo");

    // Verify it's a definition with the correct path
    // The def_path returns the canonical path (trait::method), not the impl path
    let expected_def_path = Path::from("test::Foo::foo");
    assert_eq!(sym.role, SymbolRole::Definition);
    if let SymbolIdentity::Def(target) = &sym.identity {
        let path = def_path(&result.db, target.clone())
            .map(|ip| ip.to_path())
            .expect("could not get path for impl foo definition");
        assert_eq!(path, expected_def_path);
    } else {
        panic!("expected Def identity, got {:?}", sym.identity);
    }
}

#[test]
fn collects_symbols_deref() {
    let src = r#"
fn main() {
    ptr = new(u8, 1)
    *ptr = 2
}
"#;
    let result = match test_build(src) {
        Ok(result) => result,
        Err(errs) => {
            panic!("Found errors: {:#?}", errs);
        }
    };

    let main_path = Path::from("test::main");
    let main_decl = find_func(&result.db, &main_path);
    let main_body = match &main_decl.body.as_ref().unwrap().value {
        Expr::Block(block) => block,
        _ => panic!("expected block"),
    };

    assert!(main_body.stmts.len() == 2, "expected two statements");

    let assign = match &main_body.stmts[1].value {
        Expr::Assign(assign) => assign,
        _ => panic!("expected assign"),
    };

    let assign_paths = assign.lhs.paths();
    assert!(assign_paths.len() == 1, "expected one assignment");

    let path_node = &assign_paths[0];

    // Use symbol_targets query to get symbol information
    let targets = symbol_targets(&result.db, path_node.id);

    // The deref target `ptr` should resolve to a local binding
    assert!(!targets.is_empty(), "expected symbol for ptr");
    assert!(
        targets.iter().any(|sym| {
            matches!(sym.identity, SymbolIdentity::Local(_)) && sym.role == SymbolRole::Reference
        }),
        "expected local reference for ptr, got {:?}",
        targets
    );
}

#[test]
fn collects_curly_elements() {
    let src = r#"
fn make_string() -> string {
    len = 3
    raw_ptr = new(u8, len)
    string { raw_ptr, len }
}
"#;

    let result = match test_build_with_options(src, TestBuildOptions { minimal_core: true }) {
        Ok(result) => result,
        Err(errs) => {
            panic!("Found errors: {:#?}", errs);
        }
    };

    let make_string_path = Path::from("test::make_string");
    let make_string_decl = find_func(&result.db, &make_string_path);
    let make_string_body = match &make_string_decl.body.as_ref().unwrap().value {
        Expr::Block(block) => block,
        _ => panic!("expected block"),
    };

    assert!(make_string_body.stmts.len() == 3, "expected 3 statements");

    let raw_ptr_assign = match &make_string_body.stmts[1].value {
        Expr::Assign(assign) => assign,
        _ => panic!("expected assign"),
    };

    let paths = raw_ptr_assign.lhs.paths();
    let raw_ptr_path_node = paths.first().expect("expected a single path");
    // The raw AST path is just "raw_ptr", not the fully qualified path
    assert!(raw_ptr_path_node.0.name() == Some("raw_ptr".to_string()));

    // Use symbol_targets query to check the definition site
    let def_targets = symbol_targets(&result.db, raw_ptr_path_node.id);
    let def_sym = def_targets.first().expect("expected symbol for raw_ptr definition");
    assert_eq!(def_sym.role, SymbolRole::Definition);
    assert!(
        matches!(def_sym.identity, SymbolIdentity::Local(_)),
        "expected local definition for raw_ptr"
    );

    let curly = match &make_string_body.stmts[2].value {
        Expr::Curly(curly) => curly,
        _ => panic!("expected curly"),
    };

    assert!(curly.elements.len() == 2, "expected 2 elements");

    let raw_ptr_elem = &curly.elements[0];

    // In raw AST, curly shorthand uses CurlyElement::Name
    // After transformation it becomes CurlyElement::Labeled
    let elem_node_id = match &raw_ptr_elem.value {
        CurlyElement::Name(name) => {
            // Shorthand: `raw_ptr` - the element holds both field ref and value ref
            assert_eq!(name.path.name(), Some("raw_ptr".to_string()));
            raw_ptr_elem.id
        }
        CurlyElement::Labeled(field_name, value_expr) => {
            // Explicit: `raw_ptr: raw_ptr` - the value expr holds the reference
            assert_eq!(field_name.path.name(), Some("raw_ptr".to_string()));
            value_expr.id
        }
    };

    // Use symbol_targets query to check the reference in curly element
    let targets = symbol_targets(&result.db, elem_node_id);

    // Should have the local variable reference
    assert!(
        targets.iter().any(|t| {
            matches!(t.identity, SymbolIdentity::Local(_)) && t.role == SymbolRole::Reference
        }),
        "expected local reference for raw_ptr"
    );

    // Should also have the struct field reference
    assert!(
        targets.iter().any(|t| {
            if let SymbolIdentity::Def(ref target) = t.identity {
                let path = def_path(&result.db, target.clone())
                    .map(|ip| ip.to_path());
                path == Some(Path::from("test::string::raw_ptr")) && t.role == SymbolRole::Reference
            } else {
                false
            }
        }),
        "expected struct field reference for string::raw_ptr, got {:?}",
        targets
    );
}

#[test]
#[ignore = "pending ModuleBuilder removal"]
fn collects_variable_definitions() {
    let src = r#"
fn foo(x: int, y: int) -> int {
    z = x + y
    z
}"#;

    let mut result =
        ModuleBuilder::from_src(&src, Path::from("test")).expect("Failed to build module");

    // add + op for type checking
    result.tcx.add_infix_op(
        "+".into(),
        Path::from("core::Add::+"),
        Path::from("core::Add"),
    );

    // let infer_result = InferSystem::infer(
    //     &mut result.tcx,
    //     &mut result.ncx,
    //     &result.srcmap,
    //     &result.module,
    //     &result.defs,
    // );

    // assert!(infer_result.errors.is_empty(), "Type inference failed");

    // // verify types

    // let records = collect_definition_records(&result.module, &result.srcmap, &result.tcx);

    // let foo_path = Path::from("test::foo");
    // let var_x_path = Path::from("test::foo::x");
    // let var_y_path = Path::from("test::foo::y");
    // let var_z_path = Path::from("test::foo::z");

    // assert!(records.contains_key(&foo_path));
    // assert!(records.contains_key(&var_x_path));
    // assert!(records.contains_key(&var_y_path));
    // assert!(records.contains_key(&var_z_path));

    // println!("Definition Records:\n");
    // for (path, record) in &records {
    //     println!("- {} ({}): {}", path, record.id, record);
    // }

    // println!("TyCtx: {:#?}", result.tcx);

    // // verify types
    // let x_record = records.get(&var_x_path).unwrap();
    // let x_ty = result
    //     .tcx
    //     .get_ty(x_record.id)
    //     .expect("Failed to get type for x");
    // assert_eq!(x_ty.to_string(), "int");
}

#[test]
#[ignore = "pending ModuleBuilder removal"]
fn collect_definitions_for_deref() {
    let src = r#"
trait Int['a] {
    default (uint)
}

impl Int[uint] {}

fn foo() {
    ptr = new(uint, 1)
    *ptr = 42
}"#;

    let ray_paths = RayPaths::default();
    let mut overlays = HashMap::new();
    overlays.insert("test.ray".into(), src.to_string());
    let driver = Driver::new(ray_paths);
    let options = BuildOptions {
        input_path: "test.ray".into(),
        no_core: true,
        ..Default::default()
    };
    let result = driver
        .build_frontend(&options, Some(overlays))
        .expect("Failed to build frontend");

    let records = result.definitions_by_path;

    let deref_path = Path::from("test::foo::ptr");

    assert!(records.contains_key(&deref_path));

    println!("source map: {:#?}", result.srcmap);
    println!("definitions: {:#?}", records);
    println!("symbol map: {:#?}", result.symbol_map);
}

#[test]
#[ignore = "pending ModuleBuilder removal"]
fn collects_definitions_for_trait_funcs() {
    let src = r#"
trait Addable['a] {
    fn add(self: 'a, other: 'a) -> 'a
}
"#;

    let ray_paths = RayPaths::default();
    let mut overlays = HashMap::new();
    overlays.insert("test.ray".into(), src.to_string());
    let driver = Driver::new(ray_paths);
    let options = BuildOptions {
        input_path: "test.ray".into(),
        no_core: true,
        ..Default::default()
    };
    let result = driver
        .build_frontend(&options, Some(overlays))
        .expect("Failed to build frontend");

    let records = result.definitions_by_path;

    let add_func_path = Path::from("test::Addable::['a]::add");

    assert!(records.contains_key(&add_func_path));

    println!("definitions: {:#?}", records);
}

#[test]
#[ignore = "pending ModuleBuilder removal"]
fn collects_definitions_for_impl_funcs() {
    let src = r#"
trait Foo['a] {
    fn foo(self: 'a)
}

impl Foo[int] {
    fn foo(self: int) {}
}
"#;

    let ray_paths = RayPaths::default();
    let mut overlays = HashMap::new();
    overlays.insert("test.ray".into(), src.to_string());
    let driver = Driver::new(ray_paths);
    let options = BuildOptions {
        input_path: "test.ray".into(),
        no_core: true,
        ..Default::default()
    };
    let result = driver
        .build_frontend(&options, Some(overlays))
        .expect("Failed to build frontend");

    let records = result.definitions_by_path;

    println!("records: {:#?}", records);
    println!("symbol map: {:#?}", result.symbol_map);

    let func_path = Path::from("test::Foo::[int]::foo");

    assert!(records.contains_key(&func_path));

    println!("definitions: {:#?}", records);
}
