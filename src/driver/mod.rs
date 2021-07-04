use std::{collections::HashSet, fs};

use itertools::Itertools;

use crate::{
    codegen::llvm,
    errors::{RayError, RayErrorKind},
    libgen, lir,
    pathlib::FilePath,
    sema, transform,
    typing::{state::TyEnv, ApplySubstMut, InferSystem, TyCtx},
};

mod build;

pub use build::BuildOptions;

#[derive(Debug)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
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
        let mut mod_builder = sema::ModuleBuilder::new(paths, c_include_paths);
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
        let mut lib_defs = TyEnv::new();
        let mut tcx = TyCtx::new();
        for (lib_path, lib) in mod_builder.libs {
            lib_set.insert(lib_path.clone());
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
        let (solution, defs) = match inf.infer_ty(&module, &mut srcmap, lib_defs) {
            Ok(result) => result,
            Err(errs) => {
                return Err(errs
                    .into_iter()
                    .map(|err| RayError {
                        msg: err.msg,
                        src: err.src,
                        kind: RayErrorKind::Type,
                    })
                    .collect());
            }
        };

        tcx.apply_subst_mut(&solution.subst);

        log::debug!("{}", module);

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
            log::info!("writing to {}", path);
            if let Some(err) = fs::write(path, lib).err() {
                let ray_err: RayError = err.into();
                Err(vec![ray_err])
            } else {
                Ok(())
            }
        } else {
            program.monomorphize();

            log::debug!("{}", program);

            let lcx = inkwell::context::Context::create();
            llvm::codegen(&program, &tcx, &srcmap, &lcx, output_path)
        }
    }
}
