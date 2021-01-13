use crate::{
    errors::{RayError, RayErrorKind},
    hir,
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

        // let mut ctx = mk_ctx! {
        // * => Ty::All(vec![TyVar(str!("core::deref::T"))],
        //     Box::new(Ty::Func(vec![
        //         Ty::Projection(str!("Ptr"), vec![Ty::Var(TyVar(str!("core::deref::T")))])
        //     ], Box::new(Ty::Var(TyVar(str!("core::deref::T"))))))
        // ),
        // extern fn malloc[T](size: int) -> *T
        // malloc => Ty::All(vec![TyVar(str!("core::malloc::T"))],
        //     Box::new(Ty::Func(vec![
        //         Ty::Projection(str!("Ptr"), vec![Ty::Var(TyVar(str!("core::malloc::T")))])
        //     ], Box::new(Ty::Var(TyVar(str!("core::malloc::T"))))))
        // ),
        // };
        // add_binops!(
        //     ctx,
        //     [
        //         "+", "-", "*", "/", "%", "**", ">>", "<<", "&", "|", "^", "==", "!=", ">", "<",
        //         ">=", "<="
        //     ],
        //     [int, i8, i16, i32, i64, i128, uint, u8, u16, u32, u64, u128, float, f32, f64, f128]
        // );

        // add_binops!(ctx, ["+"], [int]);

        // add_binops!(ctx, ["&&", "||"], [bool]);

        // let m = mod_builder.modules.get_mut(&mod_path).unwrap();
        let mut ctx = Ctx::new();
        let hir_mod = hir::HirModule::from_ast_module(&mod_path, &mod_builder.modules, &mut ctx)?;
        eprintln!("{}", hir_mod.root);
        let mut inf = InferSystem::new(ctx);
        match inf.infer_ty(&hir_mod.root) {
            Ok(_) => {}
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
        }

        if options.no_compile {
            return Ok(());
        }

        // generate IR
        // let prog = lir::gen()?;

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
