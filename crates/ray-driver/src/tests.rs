#![cfg(test)]

use super::*;

use ray_core::{
    ast::{Func, Impl, Node, Path},
    errors::RayError,
    libgen::collect_definition_records,
    pathlib::{FilePath, RayPaths},
    sema::{ModuleBuilder, SymbolRole},
};

fn test_build(src: &str) -> Result<FrontendResult, Vec<RayError>> {
    let filepath = FilePath::from("test.ray");
    let driver = Driver::new(RayPaths::default());
    let options = BuildOptions {
        input_path: filepath.clone(),
        no_core: true,
        ..Default::default()
    };
    let mut overlays = HashMap::new();
    overlays.insert(filepath, include_minimal_core(src));
    driver.build_frontend(&options, Some(overlays))
}

fn include_minimal_core(src: &str) -> String {
    let core = r#"
struct string {
raw_ptr: *u8
len: uint
}

trait Int['a] {
default(int)
}

impl Int[int] {}
impl Int[uint] {}
"#;
    format!("{}\n{}", core, src)
}

fn find_func<'a>(module: &'a Module<(), Decl>, path: &'a Path) -> &'a Func {
    module
        .decls
        .iter()
        .find_map(|decl| match &decl.value {
            Decl::Func(func) if &func.sig.path.value == path => Some(func),
            _ => None,
        })
        .expect(&format!("could not find function: {}", path))
}

fn find_func_in<'a>(funcs: &'a Vec<Node<Func>>, path: &'a Path) -> &'a Func {
    funcs
        .iter()
        .find_map(|decl| {
            if &decl.sig.path.value == path {
                Some(&decl.value)
            } else {
                None
            }
        })
        .expect(&format!("could not find function: {}", path))
}

fn find_impl<'a>(module: &'a Module<(), Decl>, path: &'a Path, ty: &Ty) -> &'a Impl {
    module
        .decls
        .iter()
        .find_map(|decl| match &decl.value {
            Decl::Impl(i) => {
                let impl_path = i.ty.get_path();
                let ty_param = i.ty.first_ty_param();
                if path == &impl_path && ty == ty_param {
                    Some(i)
                } else {
                    None
                }
            }
            _ => None,
        })
        .expect(&format!("could not find impl: {}", path))
}

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
    let foo_decl = find_func(&result.module, &foo_path);

    let sym = result
        .symbol_map
        .get(&foo_decl.sig.path.id)
        .and_then(|targets| targets.first())
        .expect("could not find foo symbol");
    assert_eq!(sym.path, foo_path);
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

    let trait_foo_path = Path::from("test::Foo");
    let param_ty = Ty::int();
    let impl_foo = find_impl(&result.module, &trait_foo_path, &param_ty);
    let funcs = impl_foo.funcs.as_ref().expect("impl has no functions");
    let impl_foo_path = Path::from("test::Foo::[int]::foo");
    let func = find_func_in(funcs, &impl_foo_path);

    println!("symbol_map = {:#?}", result.symbol_map);
    let sym = result
        .symbol_map
        .get(&func.sig.path.id)
        .and_then(|targets| targets.first())
        .expect("could not find symbol for int::foo");

    assert_eq!(sym.path, impl_foo_path);
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
    let main_decl = find_func(&result.module, &main_path);
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

    println!("symbol_map = {:#?}", result.symbol_map);

    let symbols = result
        .symbol_map
        .get(&path_node.id)
        .expect(&format!("could not find symbol for {}", path_node.id));

    assert!(
        symbols
            .iter()
            .any(|sym| sym.path == Path::from("test::main::ptr"))
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

    let result = match test_build(src) {
        Ok(result) => result,
        Err(errs) => {
            panic!("Found errors: {:#?}", errs);
        }
    };

    let make_string_path = Path::from("test::make_string");
    let make_string_decl = find_func(&result.module, &make_string_path);
    let make_string_body = match &make_string_decl.body.as_ref().unwrap().value {
        Expr::Block(block) => block,
        _ => panic!("expected block"),
    };

    assert!(make_string_body.stmts.len() == 3, "expected 3 statements");

    println!("body = {:#?}", make_string_body);

    let raw_ptr_assign = match &make_string_body.stmts[1].value {
        Expr::Assign(assign) => assign,
        _ => panic!("expected assign"),
    };

    let paths = raw_ptr_assign.lhs.paths();
    let raw_ptr_path_node = paths.first().expect("expected a single path");
    assert!(raw_ptr_path_node.0 == &Path::from("test::make_string::raw_ptr"));

    let sym = result
        .symbol_map
        .get(&raw_ptr_path_node.id)
        .and_then(|targets| targets.first())
        .expect("expected symbol for raw_ptr definition");
    assert_eq!(sym.path, Path::from("test::make_string::raw_ptr"));
    assert_eq!(sym.role, SymbolRole::Definition);

    let curly = match &make_string_body.stmts[2].value {
        Expr::Curly(curly) => curly,
        _ => panic!("expected curly"),
    };

    assert!(curly.elements.len() == 2, "expected 2 elements");

    let raw_ptr_elem = &curly.elements[0];
    let raw_ptr_ref_node = match &raw_ptr_elem.value {
        CurlyElement::Labeled(_, node) => node,
        _ => panic!("expected labeled element"),
    };

    println!("symbol_map = {:#?}", result.symbol_map);

    let targets = result.symbol_map.get(&raw_ptr_ref_node.id).expect(&format!(
        "could not find symbol for {}",
        raw_ptr_ref_node.id
    ));

    assert!(
        targets
            .iter()
            .any(|t| t.path == Path::from("test::make_string::raw_ptr")
                && matches!(t.role, SymbolRole::Reference))
    );
    assert!(
        targets
            .iter()
            .any(|t| t.path == Path::from("test::string::raw_ptr")
                && matches!(t.role, SymbolRole::Reference))
    );
}

#[test]
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

    let _ = InferSystem::infer(
        &mut result.tcx,
        &mut result.ncx,
        &result.srcmap,
        &result.module,
        &result.defs,
    )
    .expect("Type inference failed");

    // verify types

    let records = collect_definition_records(&result.module, &result.srcmap, &result.tcx);

    let foo_path = Path::from("test::foo");
    let var_x_path = Path::from("test::foo::x");
    let var_y_path = Path::from("test::foo::y");
    let var_z_path = Path::from("test::foo::z");

    assert!(records.contains_key(&foo_path));
    assert!(records.contains_key(&var_x_path));
    assert!(records.contains_key(&var_y_path));
    assert!(records.contains_key(&var_z_path));

    println!("Definition Records:\n");
    for (path, record) in &records {
        println!("- {} ({}): {}", path, record.id, record);
    }

    println!("TyCtx: {:#?}", result.tcx);

    // verify types
    let x_record = records.get(&var_x_path).unwrap();
    let x_ty = result
        .tcx
        .get_ty(x_record.id)
        .expect("Failed to get type for x");
    assert_eq!(x_ty.to_string(), "int");
}

#[test]
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

    let records = result.definitions;

    let deref_path = Path::from("test::foo::ptr");

    assert!(records.contains_key(&deref_path));

    println!("source map: {:#?}", result.srcmap);
    println!("definitions: {:#?}", records);
    println!("symbol map: {:#?}", result.symbol_map);
}

#[test]
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

    let records = result.definitions;

    let add_func_path = Path::from("test::Addable::['a]::add");

    assert!(records.contains_key(&add_func_path));

    println!("definitions: {:#?}", records);
}

#[test]
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

    let records = result.definitions;

    println!("records: {:#?}", records);
    println!("symbol map: {:#?}", result.symbol_map);

    let func_path = Path::from("test::Foo::[int]::foo");

    assert!(records.contains_key(&func_path));

    println!("definitions: {:#?}", records);
}
