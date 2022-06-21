use std::{collections::HashSet, fs};

use itertools::Itertools;
use top::Substitutable;

use crate::{
    codegen::llvm,
    errors::{RayError, RayErrorKind},
    libgen, lir,
    pathlib::FilePath,
    sema, transform,
    typing::{check::TypeCheckSystem, state::Env, ty::TyScheme, InferSystem, TyCtx},
};

mod build;

pub use build::BuildOptions;

#[derive(Debug, Clone)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
    pub fn get_build_path(&self) -> FilePath {
        &self.root / "build"
    }

    pub fn get_stdlib_path(&self) -> FilePath {
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
        let mod_path = mod_builder.build_from_path(&options.input_path, None)?;
        if options.print_ast {
            for m in mod_builder.modules.values() {
                eprintln!("{}", m);
            }
        }

        let mut libs = vec![];
        let mut modules = mod_builder.modules;
        let mut srcmaps = mod_builder.srcmaps;
        let mut lib_set = HashSet::new();
        let mut lib_defs = Env::new();
        let mut tcx = TyCtx::new();
        for (lib_path, mut lib) in mod_builder.libs {
            lib_set.insert(lib_path.clone());
            let curr_tyvar_idx = lib.tcx.tf().curr();
            log::debug!("curr ty var index for {}: {}", lib_path, curr_tyvar_idx);
            tcx.extend(lib.tcx);
            srcmaps.insert(lib_path, lib.srcmap);
            libs.push(lib.program);
            lib_defs.extend(lib.defs);
        }

        let (mut module, mut srcmap, _) =
            transform::combine(&mod_path, &mut modules, &mut srcmaps, &lib_set, &mut tcx)?;
        module.is_lib = options.build_lib;

        log::debug!("{}", module);
        let mut inf = InferSystem::new(&mut tcx);
        log::info!("type checking module...");
        let (solution, defs) = match inf.infer_ty(&module, &mut srcmap, lib_defs) {
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

        tcx.apply_subst(&solution.subst);
        tcx.extend_inst_ty_map(
            solution
                .inst_type_schemes
                .iter()
                .map(|(v, scheme)| (v.clone(), TyScheme::scheme(scheme.clone())))
                .collect(),
        );
        tcx.extend_scheme_subst(
            solution
                .scheme_subst()
                .into_iter()
                .map(|(v, s)| (v, TyScheme::scheme(s)))
                .collect(),
        );
        tcx.extend_predicates(solution.qualifiers.clone());

        // module.apply_subst(&solution.subst);

        log::debug!("{}", module);
        log::debug!("{}", tcx);

        // let mut tyck = TypeCheckSystem::new(&mut tcx, &srcmap);
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
        let mut program = lir::Program::gen(&module, &solution, &tcx, libs)?;
        log::debug!("{}", program);

        // determine the output path
        let output_path = |ext| {
            if let Some(outpath) = &options.output_path {
                if outpath.is_dir() {
                    let filename = mod_path.name().unwrap();
                    (outpath / filename).with_extension(ext)
                } else {
                    outpath.clone()
                }
            } else if options.build_lib && options.input_path.is_dir() {
                &options.input_path / format!(".{}", ext)
            } else {
                let filename = mod_path.name().unwrap();
                FilePath::from(filename).with_extension(ext)
            }
        };

        // if we're building a library, write the program to a .raylib file
        if options.build_lib {
            let lib = libgen::serialize(program, tcx, srcmap, defs);
            let path = output_path("raylib");
            let build_path = paths.get_build_path();
            if !build_path.exists() {
                fs::create_dir_all(build_path).map_err(|err| vec![err.into()])?;
            }

            let cache_path = (paths.get_build_path() / mod_path.join("#")).with_extension("raylib");
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
            llvm::codegen(&program, &tcx, &srcmap, &lcx, output_path)
        }
    }
}
