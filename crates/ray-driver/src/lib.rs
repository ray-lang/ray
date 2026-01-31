use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
};

use ray_codegen::{
    codegen::{CodegenOptions, llvm},
    libgen, lir, modules,
};
use ray_core::{
    ast::{Decl, Module},
    errors::{RayError, RayErrorKind},
    passes,
    sema::{SymbolBuildContext, SymbolMap, build_symbol_map},
    sourcemap::SourceMap,
};
use ray_frontend::{
    queries::{
        libraries::LoadedLibraries,
        workspace::{FileSource, WorkspaceSnapshot},
    },
    query::Database,
};
use ray_shared::{
    collections::namecontext::NameContext,
    file_id::FileId,
    node_id::NodeId,
    optlevel::OptLevel,
    pathlib::{FilePath, Path, RayPaths},
    span::Source,
};
use ray_typing::{TypecheckOptions, tyctx::TyCtx, types::Substitutable};

mod analyze;
mod build;
mod global_options;

pub use analyze::{
    AnalysisFormat, AnalysisInput, AnalysisReport, AnalyzeOptions, DefinitionInfo, SymbolInfo,
    SymbolKind, TypeInfo, collect_definitions, collect_symbols, collect_types,
};
pub use build::BuildOptions;
pub use build::EmitType;
pub use global_options::*;

pub struct FrontendResult {
    pub db: Database,
    pub file_id: FileId,
    pub module_path: Path,
    pub module: Module<(), Decl>,
    pub tcx: TyCtx,
    pub ncx: NameContext,
    pub srcmap: SourceMap,
    pub symbol_map: SymbolMap,
    pub libs: Vec<lir::Program>,
    pub paths: HashSet<Path>,
    pub definitions_by_path: HashMap<Path, libgen::DefinitionRecord>,
    pub definitions_by_id: HashMap<NodeId, libgen::DefinitionRecord>,
    pub errors: Vec<RayError>,
    pub bindings: passes::binding::BindingPassOutput,
    pub closure_analysis: passes::closure::ClosurePassOutput,
}

#[derive(Debug)]
pub struct Driver {
    ray_paths: RayPaths,
    pub errors_emitted: usize,
}

impl Driver {
    pub fn new(ray_paths: RayPaths) -> Driver {
        Driver {
            ray_paths,
            errors_emitted: 0,
        }
    }

    pub fn analyze(&mut self, options: AnalyzeOptions) -> AnalysisReport {
        let AnalyzeOptions {
            input_path,
            format,
            no_core,
        } = options;
        let build_options = BuildOptions {
            input_path: input_path.clone(),
            to_stdout: false,
            write_assembly: false,
            opt_level: OptLevel::O2,
            emit: None,
            print_ast: false,
            no_compile: true,
            target: None,
            output_path: None,
            c_include_paths: None,
            link_modules: None,
            build_lib: false,
            no_core,
        };

        match self.build_frontend(&build_options, None) {
            Ok(frontend) => {
                let input = AnalysisInput {
                    db: &frontend.db,
                    file_id: frontend.file_id,
                    decls: &frontend.module.decls,
                    srcmap: &frontend.srcmap,
                };
                let symbols = collect_symbols(&input);
                let definitions = collect_definitions(&input);
                let types = collect_types(&input);
                AnalysisReport::new(
                    format,
                    input_path,
                    frontend.module_path,
                    Vec::new(),
                    symbols,
                    types,
                    definitions,
                )
            }
            Err(errs) => AnalysisReport::new(
                format,
                input_path,
                Path::new(),
                errs,
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        }
    }

    pub fn build_frontend(
        &self,
        options: &BuildOptions,
        overlays: Option<HashMap<FilePath, String>>,
    ) -> Result<FrontendResult, Vec<RayError>> {
        let mut c_include_paths = options.c_include_paths.clone().unwrap_or_else(|| vec![]);
        let default_include = self.ray_paths.get_c_includes_path();
        if default_include.exists() && !c_include_paths.contains(&default_include) {
            c_include_paths.insert(0, default_include);
        }
        let mut mod_builder =
            modules::ModuleBuilder::new(&self.ray_paths, c_include_paths, options.no_core);
        let module_scope = match mod_builder.build(&options.input_path, overlays)? {
            Some(module_path) => module_path,
            None => return Err(mod_builder.take_errors()),
        };
        let module_path = module_scope.path;

        if options.print_ast {
            for m in mod_builder.modules.values() {
                eprintln!("{}", m);
            }
        }

        let mut result = mod_builder.finish(&module_path)?;
        result.module.is_lib = options.build_lib;

        log::debug!("{}", result.module);
        log::info!("type checking module...");

        // Run the new typechecker on the lowered module and merge its
        // schemes into the existing defs. The existing v1 pipeline remains
        // available elsewhere for parity checks.
        let tc_options = TypecheckOptions::default();
        let pass_manager = passes::FrontendPassManager::new(
            &result.module,
            &result.srcmap,
            &mut result.tcx,
            &result.resolutions,
        );
        let (binding_output, closure_output, check_result) =
            pass_manager.run_passes(&result.ncx, tc_options);

        let errors: Vec<RayError> = check_result.errors.into_iter().map(Into::into).collect();
        let definitions_by_path =
            libgen::collect_definition_records(&result.module, &result.srcmap, &result.tcx);
        let mut definitions_by_id: HashMap<NodeId, libgen::DefinitionRecord> = HashMap::new();
        for record in definitions_by_path.values() {
            definitions_by_id
                .entry(record.id)
                .or_insert_with(|| record.clone());
        }

        let symbol_map = build_symbol_map(SymbolBuildContext::new(
            &result.module,
            &result.tcx,
            &result.srcmap,
        ));

        log::debug!("[build_frontend] Frontend Summary");
        log::debug!("[build_frontend] ----------------");
        log::debug!("[build_frontend] symbol_map:");
        for (_, sym) in symbol_map.iter() {
            log::debug!(
                "[build_frontend]   {} @ {}:{}:{} (role = {:?})",
                sym.path,
                sym.filepath,
                sym.span.start.lineno + 1,
                sym.span.start.col + 1,
                sym.role,
            );
        }
        log::debug!("[build_frontend] ----------------");

        // Create a Database for query-based LIR generation
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path_for_db =
            ray_shared::pathlib::ModulePath::from(result.module.path.to_string());
        let file_id = workspace.add_file(options.input_path.clone(), module_path_for_db);
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), std::collections::HashMap::new());

        // Set file source for the main file
        let source_content = std::fs::read_to_string(&options.input_path).unwrap_or_default();
        FileSource::new(&db, file_id, source_content);

        Ok(FrontendResult {
            db,
            file_id,
            module_path,
            module: result.module,
            tcx: result.tcx,
            ncx: result.ncx,
            srcmap: result.srcmap,
            symbol_map,
            libs: result.libs,
            paths: result.paths,
            definitions_by_path,
            definitions_by_id,
            errors,
            bindings: binding_output,
            closure_analysis: closure_output,
        })
    }

    pub fn emit_errors(&mut self, errs: Vec<RayError>) {
        log::debug!("emitting errors: {:#?}", errs);

        // group the errors first by (kind, src)
        let mut groups: BTreeMap<(RayErrorKind, Vec<Source>), Vec<RayError>> = BTreeMap::new();
        for err in errs {
            let key = (err.kind, err.src.clone());
            groups.entry(key).or_default().push(err);
        }

        // then convert to a single error and emit them
        for ((kind, src), errs) in groups.into_iter() {
            let msg = errs
                .iter()
                .map(|err| err.msg.clone())
                .collect::<Vec<_>>()
                .join("\n");
            let context = errs
                .iter()
                .filter_map(|err| err.context.clone())
                .collect::<Vec<_>>()
                .join("\n");
            let err = RayError {
                msg,
                src,
                kind,
                context: Some(context),
            };
            err.emit();
            self.errors_emitted += 1;
        }
    }

    pub fn build(&self, options: BuildOptions) -> Result<(), Vec<RayError>> {
        let frontend = self.build_frontend(&options, None)?;
        if !frontend.errors.is_empty() {
            return Err(frontend.errors);
        }

        if options.no_compile {
            return Ok(());
        }

        let FrontendResult {
            db,
            file_id,
            module_path,
            module,
            tcx,
            ncx,
            srcmap,
            libs,
            paths: module_paths,
            ..
        } = frontend;

        let mut program = lir::Program::generate(&db, file_id, &module, &srcmap, libs)?;
        if matches!(options.emit, Some(build::EmitType::LIR)) {
            if !options.build_lib {
                log::debug!("program before monomorphization:\n{}", program);
                program.monomorphize();
                log::debug!("program after monomorphization:");
            }
            println!("{}", program);
            return Ok(());
        }

        log::debug!("{}", program);
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

        if options.build_lib {
            let mut modules = module_paths.into_iter().collect::<Vec<_>>();
            modules.sort();
            log::debug!("modules: {:?}", modules);

            let definitions = libgen::collect_definition_records(&module, &srcmap, &tcx);
            let lib = libgen::serialize(program, tcx, ncx, srcmap, modules, definitions);
            let path = output_path("raylib");

            log::info!("writing to {}", path);
            fs::write(path, lib).map_err(|err| vec![err.into()])
        } else {
            log::debug!("program before monomorphization:\n{}", program);
            program.monomorphize();
            log::debug!("program after monomorphization:\n{}", program);

            let lcx = inkwell::context::Context::create();
            let target = options.get_target();
            let codegen_options = CodegenOptions {
                emit: matches!(options.emit, Some(build::EmitType::LLVM)),
                opt_level: options.opt_level,
            };
            llvm::codegen(
                &program,
                &srcmap,
                &lcx,
                &target,
                output_path,
                codegen_options,
            )
        }
    }
}

#[allow(dead_code)]
fn pretty_print_tys<T>(tcx: &TyCtx, ty: &T) -> String
where
    T: Clone + Substitutable + ToString,
{
    tcx.pretty_tys(ty).to_string()
}
