use std::{collections::HashSet, fs};

use itertools::Itertools;
use top::{Subst, Substitutable};

use crate::{
    ast::{Decl, Path},
    codegen::llvm,
    errors::{RayError, RayErrorKind},
    libgen, lir,
    pathlib::FilePath,
    sema, transform,
    typing::{InferSystem, TyCtx, check::TypeCheckSystem, state::Env, ty::{Ty, TyScheme, TyVar}},
};

mod build;

pub use build::BuildOptions;

#[derive(Debug, Clone, Default)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn get_build_path(&self) -> FilePath {
        &self.root / "build"
    }

    pub fn get_lib_path(&self) -> FilePath {
        &self.root / "lib"
    }

    pub fn get_c_includes_path(&self) -> FilePath {
        &self.root / "wasi-sysroot" / "include"
    }
}

#[derive(Debug)]
pub struct Driver {
    ray_path: FilePath,
    pub errors_emitted: usize,
}

impl Driver {
    pub fn new(ray_path: FilePath) -> Driver {
        Driver {
            ray_path,
            errors_emitted: 0,
        }
    }

    pub fn emit_errors(&mut self, errs: Vec<RayError>) {
        for ((kind, src), group) in &errs.into_iter().group_by(|err| (err.kind, err.src.clone())) {
            let msg = group.map(|err| err.msg).collect::<Vec<_>>().join("\n");
            let err = RayError { msg, src, kind };
            err.emit();
            self.errors_emitted += 1;
        }
    }

    pub fn build(&self, options: BuildOptions) -> Result<(), Vec<RayError>> {
        let paths = RayPaths {
            root: self.ray_path.clone(),
        };
        let mut c_include_paths = options.c_include_paths.clone().unwrap_or_else(|| vec![]);
        c_include_paths.insert(0, paths.get_c_includes_path());
        let mut mod_builder = sema::ModuleBuilder::new(&paths, c_include_paths, options.no_core);
        let module_path = match mod_builder.build_from_path(&options.input_path, None)? {
            Some(module_path) => module_path.path,
            None => return Err(mod_builder.take_errors()),
        };

        if options.print_ast {
            for m in mod_builder.modules.values() {
                eprintln!("{}", m);
            }
        }

        let mut result = mod_builder.finish(&module_path)?;
        result.module.is_lib = options.build_lib;

        log::debug!("{}", result.module);
        let mut inf = InferSystem::new(&mut result.tcx, &mut result.ncx);
        log::info!("type checking module...");
        let (solution, defs) = match inf.infer_ty(&result.module, &mut result.srcmap, result.defs) {
            Ok(result) => result,
            Err(errs) => {
                return Err(errs
                    .into_iter()
                    .map(|err| RayError {
                        msg: err.message(),
                        src: err.src,
                        kind: RayErrorKind::Type,
                    })
                    .collect());
            }
        };

        log::debug!("solution: {}", solution);
        log::debug!("defs: {}", defs);

        result.tcx.apply_subst(&solution.subst);
        let inst_scheme_map = solution
            .inst_type_schemes
            .iter()
            .map(|(v, scheme)| {
                let ty_scheme = TyScheme::scheme(scheme.clone());
                log::debug!(
                    "inst_type_schemes: inserting {} => {} (has_quantifiers={})",
                    v,
                    ty_scheme,
                    ty_scheme.has_quantifiers()
                );
                (v.clone(), ty_scheme)
            })
            .collect();
        result.tcx.extend_inst_ty_map(inst_scheme_map);
        let inst_scheme_keys = solution
            .inst_type_schemes
            .keys()
            .cloned()
            .collect::<HashSet<_>>();

        let mut poly_inst_seeds = Subst::<TyVar, TyScheme>::new();
        {
            let tcx = &result.tcx;
            let defs_ref = &defs;

            let mut seed_from_fn = |node_id: u64, path: &Path| {
                if let Some(Ty::Var(original_tv)) = tcx.original_ty_of(node_id) {
                    if tcx.inst_ty_of(original_tv).is_some() {
                        log::debug!(
                            "poly_inst_seed: {} already has instantiation; skipping path {}",
                            original_tv,
                            path
                        );
                        return;
                    }

                    if let Some(scheme) = defs_ref.get(path) {
                        if scheme.has_quantifiers() {
                            log::debug!(
                                "poly_inst_seed: seeding {} with polymorphic scheme {} from {}",
                                original_tv,
                                scheme,
                                path
                            );
                            poly_inst_seeds.insert(original_tv.clone(), scheme.clone());
                        } else {
                            log::debug!(
                                "poly_inst_seed: defs entry for {} is monomorphic {}; skipping",
                                path,
                                scheme
                            );
                        }
                    } else {
                        log::debug!(
                            "poly_inst_seed: no defs entry for {}; skipping",
                            path
                        );
                    }
                }
            };

            for decl in &result.module.decls {
                match &decl.value {
                    Decl::Func(func) => seed_from_fn(decl.id, &func.sig.path),
                    Decl::Impl(imp) => {
                        if let Some(funcs) = &imp.funcs {
                            for func in funcs {
                                seed_from_fn(func.id, &func.sig.path);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        if !poly_inst_seeds.is_empty() {
            result.tcx.extend_inst_ty_map(poly_inst_seeds);
        }

        let filtered_scheme_subst = solution
            .scheme_subst()
            .into_iter()
            .filter_map(|(v, s)| {
                if inst_scheme_keys.contains(&v) {
                    log::debug!(
                        "scheme_subst: skipping {} because instantiation exists",
                        v
                    );
                    return None;
                }
                let scheme = TyScheme::scheme(s);
                if scheme.has_quantifiers() {
                    log::debug!(
                        "scheme_subst: dropping {} => {} (has_quantifiers)",
                        v,
                        scheme
                    );
                    None
                } else {
                    log::debug!("scheme_subst: keeping {} => {}", v, scheme);
                    Some((v, scheme))
                }
            })
            .collect();
        result.tcx.extend_scheme_subst(filtered_scheme_subst);
        result.tcx.extend_predicates(solution.qualifiers.clone());
        result.tcx.tf().skip_to(solution.unique as u64);

        // module.apply_subst(&solution.subst);

        log::debug!("{}", result.module);
        log::debug!("{}", result.tcx);

        // let mut tyck = TypeCheckSystem::new(&mut result.tcx, &srcmap);
        // if let Err(err) = tyck.type_check(&mut module) {
        //     return Err(vec![RayError {
        //         msg: err.message(),
        //         src: err.src,
        //         kind: RayErrorKind::Type,
        //     }]);
        // }

        if options.no_compile {
            return Ok(());
        }

        // generate IR
        let mut program = lir::Program::generate(
            &result.module,
            &solution,
            &result.tcx,
            &result.srcmap,
            result.libs,
        )?;
        log::debug!("{}", program);

        // determine the output path
        let output_path = |ext| {
            if let Some(outpath) = &options.output_path {
                if outpath.is_dir() {
                    let filename = module_path.name().unwrap();
                    (outpath / filename).with_extension(ext)
                } else {
                    outpath.clone()
                }
            } else if options.build_lib && options.input_path.is_dir() {
                &options.input_path / format!(".{}", ext)
            } else {
                let filename = module_path.name().unwrap();
                FilePath::from(filename).with_extension(ext)
            }
        };

        // if we're building a library, write the program to a .raylib file
        if options.build_lib {
            let mut modules = result.paths.into_iter().collect::<Vec<_>>();
            modules.sort();
            log::debug!("modules: {:?}", modules);
            let lib = libgen::serialize(
                program,
                result.tcx,
                result.ncx,
                result.srcmap,
                defs,
                modules,
            );
            let path = output_path("raylib");
            let build_path = paths.get_build_path();
            if !build_path.exists() {
                fs::create_dir_all(build_path).map_err(|err| vec![err.into()])?;
            }

            let cache_path =
                (paths.get_build_path() / module_path.join("#")).with_extension("raylib");
            log::info!("writing to {}", path);
            // write to the build cache first
            fs::write(cache_path, &lib)
                .and_then(|_| fs::write(path, lib))
                .map_err(|err| vec![err.into()])
        } else {
            log::debug!("program before monomorphization:\n{}", program);
            program.monomorphize();
            log::debug!("program after monomorphization:\n{}", program);

            let lcx = inkwell::context::Context::create();
            let target = options.get_target();
            llvm::codegen(
                &program,
                &result.tcx,
                &result.srcmap,
                &lcx,
                &target,
                output_path,
            )
        }
    }
}
