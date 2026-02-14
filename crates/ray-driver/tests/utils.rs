#![cfg(test)]

use std::collections::HashMap;

use ray_core::{
    ast::{Decl, Func, Impl, Node},
    errors::RayError,
};
use ray_driver::*;
use ray_frontend::{
    queries::{
        defs::def_path, parse::parse_file, resolve::name_resolutions, workspace::WorkspaceSnapshot,
    },
    query::Database,
};
use ray_shared::resolution::{DefTarget, Resolution};
use ray_shared::{
    pathlib::{FilePath, Path, RayPaths},
    ty::Ty,
};

#[derive(Debug, Default)]
pub struct TestBuildOptions {
    pub(crate) minimal_core: bool,
}

#[allow(dead_code)]
pub fn enable_debug_logs() {
    fern::Dispatch::new()
        .level(log::LevelFilter::Debug)
        .chain(std::io::stderr())
        .apply()
        .unwrap();
}

#[allow(dead_code)]
pub fn test_workspace(src: &str) -> Result<WorkspaceResult, Vec<RayError>> {
    test_workspace_with_options(src, TestBuildOptions::default())
}

#[allow(dead_code)]
pub fn test_workspace_with_options(
    src: &str,
    test_options: TestBuildOptions,
) -> Result<WorkspaceResult, Vec<RayError>> {
    let filepath = FilePath::from("test.ray");
    let driver = Driver::new(RayPaths::default(), None);
    let options = BuildOptions {
        input_path: filepath.clone(),
        no_core: true,
        ..Default::default()
    };
    let mut overlays = HashMap::new();
    if test_options.minimal_core {
        overlays.insert(filepath, include_minimal_core(src));
    } else {
        overlays.insert(filepath, src.to_string());
    }
    driver.init_workspace(&options, Some(overlays))
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

/// Find a function declaration by path using queries.
///
/// Searches all files in the workspace for a function with the given path.
#[allow(dead_code)]
pub fn find_func(db: &Database, path: &Path) -> Func {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        for decl in &parse_result.ast.decls {
            if let Decl::Func(func) = &decl.value {
                if &func.sig.path.value == path {
                    return func.clone();
                }
            }
        }
    }
    panic!("could not find function: {}", path)
}

/// Find a function within a list of declarations (e.g., impl funcs).
#[allow(dead_code)]
pub fn find_func_in(funcs: &[Node<Decl>], path: &Path) -> Func {
    funcs
        .iter()
        .find_map(|decl| {
            let Decl::Func(func) = &decl.value else {
                return None;
            };
            if &func.sig.path.value == path {
                Some(func.clone())
            } else {
                None
            }
        })
        .expect(&format!("could not find function: {}", path))
}

/// Find an impl declaration by resolved trait path and type parameter using queries.
///
/// Searches all files in the workspace for an impl whose trait type resolves to
/// the given path. Uses name resolution to get the qualified path.
///
/// For `impl Foo[int]`, pass `path = "test::Foo"` and `ty = Ty::int()`.
#[allow(dead_code)]
pub fn find_impl(db: &Database, trait_path: &Path, impl_ty: &Ty) -> Impl {
    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        let resolutions = name_resolutions(db, file_id);

        for decl in &parse_result.ast.decls {
            if let Decl::Impl(i) = &decl.value {
                // Get the synthetic IDs for the impl type (e.g., [Foo_id, int_id] for Foo[int])
                let synthetic_ids = i.ty.synthetic_ids();
                if synthetic_ids.is_empty() {
                    continue;
                }

                // First synthetic ID is the trait/base type
                let trait_node_id = synthetic_ids[0];
                let Some(Resolution::Def(DefTarget::Workspace(trait_def_id))) =
                    resolutions.get(&trait_node_id)
                else {
                    continue;
                };

                // Get the resolved path for the trait
                let Some(resolved_trait_path) =
                    def_path(db, DefTarget::Workspace(*trait_def_id)).map(|ip| ip.to_path())
                else {
                    continue;
                };

                // Check if trait path matches and type argument matches
                let ty_param = i.ty.first_type_argument();
                if &resolved_trait_path == trait_path && ty_param == impl_ty {
                    return i.clone();
                }
            }
        }
    }
    panic!("could not find impl: {}", trait_path)
}
