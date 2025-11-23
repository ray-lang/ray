#![cfg(test)]

use std::collections::HashMap;

use ray_typing::ty::Ty;
use ray_core::{
    ast::{Decl, Func, Impl, Module, Node},
    errors::RayError,
};
use ray_driver::*;
use ray_shared::pathlib::{FilePath, Path, RayPaths};

#[allow(dead_code)]
pub fn enable_debug_logs() {
    fern::Dispatch::new()
        .level(log::LevelFilter::Debug)
        .chain(std::io::stderr())
        .apply()
        .unwrap();
}

pub fn test_build(src: &str) -> Result<FrontendResult, Vec<RayError>> {
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

pub fn include_minimal_core(src: &str) -> String {
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

#[allow(dead_code)]
pub fn find_func<'a>(module: &'a Module<(), Decl>, path: &'a Path) -> &'a Func {
    module
        .decls
        .iter()
        .find_map(|decl| match &decl.value {
            Decl::Func(func) if &func.sig.path.value == path => Some(func),
            _ => None,
        })
        .expect(&format!("could not find function: {}", path))
}

#[allow(dead_code)]
pub fn find_func_in<'a>(funcs: &'a Vec<Node<Func>>, path: &'a Path) -> &'a Func {
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

#[allow(dead_code)]
pub fn find_impl<'a>(module: &'a Module<(), Decl>, path: &'a Path, ty: &Ty) -> &'a Impl {
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
