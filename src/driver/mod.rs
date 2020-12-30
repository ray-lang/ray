use crate::{
    add_binops,
    errors::{RayError, RayErrorKind},
    hir, mk_binop_ty, mk_ctx,
    pathlib::FilePath,
    sema,
    typing::{
        ty::{Ty, TyVar},
        InferSystem,
    },
};

use itertools::Itertools;

mod build;

pub use build::BuildOptions;

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

    pub fn get_stdlib_path(&self) -> FilePath {
        &self.ray_path / "lib"
    }

    pub fn get_c_includes_path(&self) -> FilePath {
        &self.ray_path / "wasi-sysroot" / "include"
    }

    pub fn emit_errors(&mut self, errs: Vec<RayError>) {
        for ((kind, span, fp), group) in &errs
            .into_iter()
            .group_by(|err| (err.kind, err.span, err.fp.clone()))
        {
            let msg = group.map(|err| err.msg).collect::<Vec<_>>().join("\n");
            let err = RayError {
                msg,
                fp,
                kind,
                span,
            };
            err.emit();
            self.errors_emitted += 1;
        }
    }

    pub fn build(&self, options: BuildOptions) -> Result<(), Vec<RayError>> {
        let libpath = self.get_stdlib_path();
        let mut c_include_paths = options.c_include_paths.unwrap_or_else(|| vec![]);
        c_include_paths.insert(0, self.get_c_includes_path());
        let mut mod_builder = sema::ModuleBuilder::new(libpath, c_include_paths);
        let mod_path = mod_builder.build_from_path(&options.input_path, None)?;
        if options.print_ast {
            for m in mod_builder.modules.values() {
                eprintln!("{}", m);
            }
        }

        let mut ctx = mk_ctx! {
            * => Ty::All(vec![TyVar(str!("core::deref::T"))],
                Box::new(Ty::Func(vec![
                    Ty::Projection(str!("Ptr"), vec![Ty::Var(TyVar(str!("core::deref::T")))])
                ], Box::new(Ty::Var(TyVar(str!("core::deref::T"))))))
            ),
            // extern fn malloc[T](size: int) -> *T
            // malloc => Ty::All(vec![TyVar(str!("core::malloc::T"))],
            //     Box::new(Ty::Func(vec![
            //         Ty::Projection(str!("Ptr"), vec![Ty::Var(TyVar(str!("core::malloc::T")))])
            //     ], Box::new(Ty::Var(TyVar(str!("core::malloc::T"))))))
            // ),
        };
        add_binops!(
            ctx,
            [
                "+", "-", "*", "/", "%", "**", ">>", "<<", "&", "|", "^", "==", "!=", ">", "<",
                ">=", "<="
            ],
            [int, i8, i16, i32, i64, i128, uint, u8, u16, u32, u64, u128, float, f32, f64, f128]
        );

        add_binops!(ctx, ["&&", "||"], [bool]);

        // let m = mod_builder.modules.get_mut(&mod_path).unwrap();
        let hir_mod = hir::HirModule::from_ast_module(&mod_path, &mod_builder.modules, &mut ctx)?;
        let inf = InferSystem::new(ctx);
        eprintln!("{}", hir_mod.root);
        match inf.infer_ty(hir_mod.root) {
            Ok((ex, _)) => eprintln!("type: `{}`", ex.get_type()),
            Err(err) => {
                return Err(vec![RayError {
                    msg: err.msg,
                    fp: options.input_path,
                    kind: RayErrorKind::Type,
                    span: err.metadata,
                }]);
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
