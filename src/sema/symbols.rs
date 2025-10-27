use crate::ast::{
    Assign, Curly, CurlyElement, Decl, Expr, Func, FuncSig, Module, Path, WalkItem, walk_module,
};
use crate::pathlib::FilePath;
use crate::span::Span;
use crate::span::{Source, SourceMap};
use crate::typing::ty::Ty;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolRole {
    Definition,
    Reference,
}

#[derive(Debug, Clone)]
pub struct SymbolTarget {
    pub path: Path,
    pub filepath: FilePath,
    pub span: Span,
    pub role: SymbolRole,
}

#[derive(Debug, Default, Clone)]
pub struct SymbolMap {
    entries: HashMap<u64, Vec<SymbolTarget>>,
}

impl SymbolMap {
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    pub fn insert(&mut self, node_id: u64, target: SymbolTarget) {
        self.entries.entry(node_id).or_default().push(target);
    }

    pub fn get(&self, node_id: &u64) -> Option<&[SymbolTarget]> {
        self.entries.get(node_id).map(|targets| targets.as_slice())
    }

    pub fn iter(&self) -> impl Iterator<Item = (u64, &SymbolTarget)> {
        self.entries.iter().flat_map(|(id, targets)| {
            let id = *id;
            targets.iter().map(move |target| (id, target))
        })
    }
}

pub(crate) struct SymbolBuildContext<'a> {
    module: &'a Module<(), Decl>,
    srcmap: &'a SourceMap,
    symbol_map: SymbolMap,
    definitions: HashMap<Path, SymbolTarget>,
    struct_fields: HashMap<(String, String), Path>,
}

impl<'a> SymbolBuildContext<'a> {
    pub(crate) fn new(
        module: &'a Module<(), Decl>,
        srcmap: &'a SourceMap,
    ) -> SymbolBuildContext<'a> {
        SymbolBuildContext {
            module,
            srcmap,
            symbol_map: SymbolMap::new(),
            definitions: HashMap::new(),
            struct_fields: HashMap::new(),
        }
    }

    fn record_definition(&mut self, node_id: u64, path: &Path, source: &Source) {
        if path.is_empty() {
            return;
        }

        let Some(span) = source.span else {
            return;
        };

        let target = SymbolTarget {
            path: path.clone(),
            filepath: source.filepath.clone(),
            span,
            role: SymbolRole::Definition,
        };

        self.symbol_map.insert(node_id, target.clone());
        self.definitions.insert(path.clone(), target);
    }

    fn record_reference(&mut self, node_id: u64, path: &Path) {
        if let Some(targets) = self.symbol_map.get(&node_id) {
            if targets.iter().any(|existing| {
                existing.path == *path && matches!(existing.role, SymbolRole::Reference)
            }) {
                return;
            }
        }

        if let Some(target) = self.definitions.get(path) {
            let mut target = target.clone();
            target.role = SymbolRole::Reference;
            self.symbol_map.insert(node_id, target);
        }
    }

    fn record_assign(&mut self, assign: &Assign) {
        for node in assign.lhs.paths() {
            let (path, is_lvalue) = node.value;
            if !is_lvalue {
                let source = self.srcmap.get_by_id(node.id).unwrap();
                self.record_definition(node.id, &path, &source);
            } else {
                self.record_reference(node.id, &path);
            }
        }
    }

    fn record_func_sig(&mut self, sig: &FuncSig) {
        if let Some(sig_source) = self.srcmap.get_by_id(sig.path.id) {
            self.record_definition(sig.path.id, &sig.path, &sig_source);
        }

        for param in sig.params.iter() {
            if let Some(param_source) = self.srcmap.get_by_id(param.id) {
                self.record_definition(param.id, param.name(), &param_source);
            }
        }
    }

    fn record_struct_literal(&mut self, curly: &Curly) {
        let Some(lhs) = &curly.lhs else {
            return;
        };

        let struct_path = lhs.value().clone();
        let struct_name = struct_path
            .name()
            .unwrap_or_else(|| struct_path.to_string());

        for element in &curly.elements {
            if let CurlyElement::Labeled(field_name, expr) = &element.value {
                let field_ident = field_name
                    .path
                    .name()
                    .unwrap_or_else(|| field_name.path.to_string());

                if let Some(field_path) = self
                    .struct_fields
                    .get(&(struct_name.clone(), field_ident.clone()))
                {
                    let field_path = field_path.clone();
                    self.record_reference(expr.id, &field_path);
                } else {
                    let fallback_path = struct_path.append(field_ident);
                    self.record_reference(expr.id, &fallback_path);
                }
            }
        }
    }
}

pub(crate) fn build_symbol_map(mut ctx: SymbolBuildContext<'_>) -> SymbolMap {
    // TODO: walk the module with `walk_module(ctx.module)` and populate `map`
    // using the source information from `ctx.srcmap`.
    for item in walk_module(ctx.module) {
        match item {
            WalkItem::Decl(decl) => match &decl.value {
                Decl::Mutable(node) | Decl::Name(node) => {
                    if let Some(source) = ctx.srcmap.get_by_id(node.id) {
                        ctx.record_definition(node.id, &node.path, &source);
                    }
                }
                Decl::Trait(tr) => {
                    let trait_src = ctx.srcmap.get(&tr.path);
                    ctx.record_definition(tr.path.id, &tr.path, &trait_src);
                }
                Decl::Struct(st) => {
                    let struct_path = st.path.value.clone();
                    let struct_name = struct_path.name().unwrap();
                    if !Ty::is_builtin_name(&struct_name) {
                        let name_src = ctx.srcmap.get(&st.path);
                        ctx.record_definition(st.path.id, &struct_path, &name_src);
                    }

                    if let Some(fields) = &st.fields {
                        for field in fields {
                            let field_source = ctx.srcmap.get(field);
                            let field_name = field
                                .value
                                .path
                                .name()
                                .unwrap_or_else(|| field.value.path.to_string());
                            let field_path = struct_path.append(field_name.clone());
                            ctx.record_definition(field.id, &field_path, &field_source);
                            ctx.struct_fields
                                .insert((struct_name.to_string(), field_name), field_path);
                        }
                    }
                }
                Decl::Func(Func { sig, .. }) | Decl::FnSig(sig) => {
                    ctx.record_func_sig(sig);
                }
                Decl::Declare(assign) => ctx.record_assign(assign),
                Decl::Extern(_) | Decl::Impl(_) | Decl::TypeAlias(_, _) => continue,
            },
            WalkItem::Expr(expr) => match &expr.value {
                Expr::Name(name) => {
                    ctx.record_reference(expr.id, &name.path);
                }
                Expr::Path(path) => {
                    ctx.record_reference(expr.id, path);
                }
                Expr::Assign(assign) => ctx.record_assign(assign),
                Expr::Func(func) => ctx.record_func_sig(&func.sig),
                Expr::Curly(curly) => ctx.record_struct_literal(curly),
                _ => continue,
            },
            WalkItem::Func(func) => {
                ctx.record_func_sig(&func.sig);
            }
            WalkItem::Name(node) => {
                ctx.record_reference(node.id, &node.path);
            }
            WalkItem::CurlyElement(element) => match &element.value {
                CurlyElement::Name(name) => {
                    ctx.record_reference(element.id, &name.path);
                }
                CurlyElement::Labeled(_, _) => continue,
            },
            _ => continue,
        }
    }

    ctx.symbol_map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{Func, Impl, Node, Path},
        driver::{BuildOptions, Driver, FrontendResult, RayPaths},
        errors::RayError,
        pathlib::FilePath,
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
                    let impl_path = i.ty.get_path().unwrap();
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
}
