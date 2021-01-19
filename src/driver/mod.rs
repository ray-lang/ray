use crate::{
    errors::{RayError, RayErrorKind},
    hir, lir,
    pathlib::FilePath,
    sema,
    typing::{Ctx, InferSystem},
};

mod build;

pub use build::BuildOptions;
use itertools::Itertools;

#[derive(Debug)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
    pub fn get_stdlib_path(&self) -> FilePath {
        &self.root / "lib"
    }

    pub fn get_src_path(&self) -> FilePath {
        &self.root / "src"
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
        let mut c_include_paths = options.c_include_paths.unwrap_or_else(|| vec![]);
        c_include_paths.insert(0, paths.get_c_includes_path());
        let mut mod_builder = sema::ModuleBuilder::new(paths, c_include_paths);
        let mod_path = mod_builder.build_from_path(&options.input_path, None)?;
        if options.print_ast {
            for m in mod_builder.modules.values() {
                eprintln!("{}", m);
            }
        }

        let mut modules = mod_builder.modules;
        let mut ctx = Ctx::new();
        let hir_mod = hir::transform_modules(&mod_path, &mut modules, &mut ctx)?;
        log::debug!("{}", hir_mod);
        let mut inf = InferSystem::new(ctx);
        let typed_mod = match inf.infer_ty(hir_mod) {
            Ok(m) => m,
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

        log::debug!("{}", typed_mod);

        if options.no_compile {
            return Ok(());
        }

        // generate IR
        // let mut prog = lir::Program::gen(mod_path, typed_mod)?;
        // prog.monomorphize();
        // eprintln!("{}", prog);

        // compile to asm
        Ok(())

        // parseOpts := &parse.ParseOptions{
        //     FilePath:      options.InputFilename,
        //     Cache:         parse.NewModuleCache(),
        //     Target:        tgt,
        //     UseStdin:      false,
        //     StdlibPath:    r.getStdlibPath(),
        //     NoStdlib:      options.NoStdlib,
        //     CursorLoc:     nil,
        //     CIncludePaths: append(r.defaultCIncludesPaths(), options.CIncludePaths...),
        // }
        // mod, _, err := r.ParseAndTypeCheck(options.InputFilename, parseOpts)
        // if err != nil {
        //     return err
        // }

        // if options.PrintAST {
        //     if options.OutputPath != "" {
        //         f, err := os.OpenFile(options.OutputPath, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0644)
        //         if err != nil {
        //             return err
        //         }
        //         return astprinter.Fprint(f, mod)
        //     }
        //     return astprinter.Print(mod)
        // }

        // if options.NoCompile {
        //     return nil
        // }

        // // gen := ir.NewGen(mod, options.BuildLib)
        // // prog := gen.Compile(mod, tcx)
        // // prog.WriteTo(os.Stdout)

        // panic("compile unimplemented")

        // // var c compile.Compiler
        // // switch tgt {
        // // case target.WASM:
        // // 	// TODO: make stack size configurable
        // // 	linkModules := append(r.defaultWASIModules(), options.LinkModules...)
        // // 	c = wasm.NewCompiler(options.InputFilename, linkModules, uint32(math.Pow(2, 16))) // 64 KiB
        // // default:
        // // 	panic(fmt.Sprintf("Unsupported target %s", tgt))
        // // }

        // // copts := compile.NewOptions()
        // // copts.BuildLib = options.BuildLib
        // // copts.ToStdout = options.ToStdout
        // // copts.WriteAssembly = options.WriteAssembly
        // // copts.OutputPath = options.OutputPath
        // // copts.EmitIR = options.EmitIR
        // // copts.MaxOptimizeLevel = options.MaxOptimizeLevel
        // // return compile.Compile(c, m, tcx, copts)
    }
}
