use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
};

use ray_codegen::{
    codegen::{CodegenOptions, llvm},
    libgen, lir,
};
use ray_core::{
    ast::{Decl, Module},
    errors::{RayError, RayErrorKind},
    passes,
    sema::SymbolMap,
    sourcemap::SourceMap,
};
use ray_frontend::{
    queries::{
        libraries::{LibraryData, LoadedLibraries},
        transform::file_ast,
        workspace::WorkspaceSnapshot,
    },
    query::Database,
};
use ray_shared::{
    collections::namecontext::NameContext,
    file_id::FileId,
    node_id::NodeId,
    optlevel::OptLevel,
    pathlib::{FilePath, ModulePath, Path, RayPaths},
    span::Source,
};
use ray_typing::{tyctx::TyCtx, types::Substitutable};

mod analyze;
mod build;
mod discovery;
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
        // Build search paths for library resolution
        let mut search_paths = vec![self.ray_paths.get_lib_path()];
        if let Some(link_paths) = &options.link_modules {
            search_paths.extend(link_paths.iter().cloned());
        }

        // Create database first
        let db = Database::new();

        // Run discovery to populate workspace and libraries
        let discovery_options = discovery::DiscoveryOptions {
            no_core: options.no_core,
            build_lib: options.build_lib,
        };
        let (workspace, loaded_libs) = discovery::discover_workspace(
            &db,
            &options.input_path,
            search_paths,
            discovery_options,
            overlays.as_ref(),
        )
        .map_err(|e| vec![e])?;

        // Get entry file info
        let file_id = workspace.entry.ok_or_else(|| {
            vec![RayError {
                msg: "no entry file in workspace".to_string(),
                src: vec![],
                kind: RayErrorKind::Compile,
                context: None,
            }]
        })?;

        let file_info = workspace.file_info(file_id).ok_or_else(|| {
            vec![RayError {
                msg: "entry file not found in workspace".to_string(),
                src: vec![],
                kind: RayErrorKind::Compile,
                context: None,
            }]
        })?;

        let module_path = Path::from(file_info.module_path.to_string());

        // Collect module paths for library generation
        let paths: HashSet<Path> = workspace
            .all_module_paths()
            .map(|mp| Path::from(mp.to_string()))
            .collect();

        // Set the workspace as input (in case discovery modified it)
        db.set_input::<WorkspaceSnapshot>((), workspace.clone());

        // Set loaded libraries as input
        LoadedLibraries::new(&db, (), loaded_libs.libraries, loaded_libs.library_files);

        // Build combined source map from all file ASTs
        let mut combined_srcmap = SourceMap::new();
        let mut all_errors: Vec<RayError> = Vec::new();

        for fid in workspace.all_file_ids() {
            let file_ast_result = file_ast(&db, fid);
            combined_srcmap.extend_with(file_ast_result.source_map.clone());
            all_errors.extend(file_ast_result.errors.clone());
        }

        if options.print_ast {
            for fid in workspace.all_file_ids() {
                let file_ast_result = file_ast(&db, fid);
                // Note: File doesn't impl Debug, so we just print decls
                for decl in &file_ast_result.ast.decls {
                    eprintln!("{}", decl);
                }
            }
        }

        log::debug!("[build_frontend] Frontend Summary");
        log::debug!("[build_frontend] ----------------");
        log::debug!(
            "[build_frontend] files: {:?}",
            workspace.all_file_ids().collect::<Vec<_>>()
        );
        log::debug!("[build_frontend] modules: {:?}", paths);
        log::debug!("[build_frontend] errors: {:?}", all_errors.len());
        log::debug!("[build_frontend] ----------------");

        // Create placeholder values for legacy fields
        // These are deprecated and will be removed as we migrate to queries
        let empty_module = Module {
            path: module_path.clone(),
            stmts: vec![],
            decls: vec![],
            imports: vec![],
            import_stmts: vec![],
            submodules: vec![],
            doc_comment: None,
            root_filepath: options.input_path.clone(),
            filepaths: vec![options.input_path.clone()],
            is_lib: options.build_lib,
        };
        let empty_tcx = TyCtx::default();
        let empty_ncx = NameContext::new();

        Ok(FrontendResult {
            db,
            file_id,
            module_path,
            module: empty_module,
            tcx: empty_tcx,
            ncx: empty_ncx,
            srcmap: combined_srcmap,
            symbol_map: SymbolMap::new(),
            paths,
            definitions_by_path: HashMap::new(),
            definitions_by_id: HashMap::new(),
            errors: all_errors,
            bindings: passes::binding::BindingPassOutput::empty(),
            closure_analysis: passes::closure::ClosurePassOutput::default(),
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
            module_path,
            srcmap,
            paths: module_paths,
            ..
        } = frontend;

        let mut program = lir::generate(&db, options.build_lib)?;
        if matches!(options.emit, Some(build::EmitType::LIR)) {
            if !options.build_lib {
                log::debug!("program before monomorphization:\n{}", program);
                lir::monomorphize(&mut program);
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

            // TODO: build_library_data() should populate LibraryData from queries
            // For now, create a minimal LibraryData with just modules and source_map
            let lib_data = LibraryData {
                modules: modules
                    .into_iter()
                    .map(|p| ModulePath::from(p.to_string().as_str()))
                    .collect(),
                source_map: srcmap.clone(),
                ..Default::default()
            };
            let lib = libgen::serialize(lib_data, program);
            let path = output_path("raylib");

            log::info!("writing to {}", path);
            fs::write(path, lib).map_err(|err| vec![err.into()])
        } else {
            log::debug!("program before monomorphization:\n{}", program);
            lir::monomorphize(&mut program);
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
