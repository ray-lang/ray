use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    path::PathBuf,
};

use ray_codegen::{
    codegen::{CodegenOptions, llvm},
    libgen, lir,
};
use ray_core::{
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_frontend::{
    queries::{
        diagnostics::workspace_diagnostics,
        libraries::{LoadedLibraries, build_library_data},
        transform::file_ast,
        workspace::{WorkspaceSnapshot, workspace_source_map},
    },
    query::Database,
};
use ray_shared::{
    file_id::FileId,
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
    AnalysisFormat, AnalysisReport, AnalyzeOptions, DefinitionInfo, SymbolInfo, SymbolKind,
    TypeInfo, collect_definitions, collect_symbols, collect_types,
};
pub use build::BuildOptions;
pub use build::EmitType;
pub use global_options::*;

/// Result of workspace initialization.
///
/// Contains the database with all inputs set and the entry file ID.
/// Use queries to get diagnostics, source maps, and other derived data:
/// - `workspace_diagnostics(&db, ())` for all errors
/// - `workspace_source_map(&db, ())` for combined source map
/// - `workspace.all_module_paths()` for module paths
pub struct WorkspaceResult {
    pub db: Database,
    pub entry_file: FileId,
}

impl WorkspaceResult {
    /// Get the entry module path from the workspace.
    pub fn entry_module_path(&self) -> Path {
        let workspace = self.db.get_input::<WorkspaceSnapshot>(());
        workspace
            .file_info(self.entry_file)
            .map(|info| Path::from(info.module_path.to_string()))
            .unwrap_or_else(Path::new)
    }

    /// Get all module paths in the workspace.
    pub fn module_paths(&self) -> HashSet<Path> {
        let workspace = self.db.get_input::<WorkspaceSnapshot>(());
        workspace
            .all_module_paths()
            .map(|mp| Path::from(mp.to_string()))
            .collect()
    }
}

/// Legacy result type for backward compatibility.
///
/// Prefer using `WorkspaceResult` from `init_workspace()` and queries instead.
#[deprecated(note = "Use WorkspaceResult from init_workspace() and queries instead")]
pub struct FrontendResult {
    pub db: Database,
    pub file_id: FileId,
    pub module_path: Path,
    pub srcmap: SourceMap,
    pub paths: HashSet<Path>,
    pub errors: Vec<RayError>,
}

#[derive(Debug)]
pub struct Driver {
    ray_paths: RayPaths,
    workspace_root: Option<PathBuf>,
    pub errors_emitted: usize,
}

impl Driver {
    /// Create a new Driver.
    ///
    /// If `config_path` points to a `ray.toml` file, its parent directory is
    /// used as the workspace root for disk caching. Otherwise, the current
    /// working directory is checked for a `ray.toml`.
    pub fn new(ray_paths: RayPaths, config_path: Option<&std::path::Path>) -> Driver {
        let workspace_root = Self::resolve_workspace_root(config_path);
        if let Some(ref root) = workspace_root {
            log::info!("workspace root: {}", root.display());
        }
        Driver {
            ray_paths,
            workspace_root,
            errors_emitted: 0,
        }
    }

    fn resolve_workspace_root(config_path: Option<&std::path::Path>) -> Option<PathBuf> {
        let config = if let Some(path) = config_path {
            if path.exists() {
                Some(path.to_path_buf())
            } else {
                log::warn!("--config-path {:?} does not exist", path);
                None
            }
        } else {
            ray_cfg::find_project_config()
        };
        config.and_then(|p| p.parent().map(|d| d.to_path_buf()))
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

        match self.init_workspace(&build_options, None) {
            Ok(workspace) => {
                let symbols = collect_symbols(&workspace.db);
                let definitions = collect_definitions(&workspace.db);
                let types = collect_types(&workspace.db);
                let module_path = workspace.entry_module_path();

                if let Err(e) = workspace.db.flush_cache() {
                    log::warn!("failed to flush cache: {}", e);
                }

                AnalysisReport::new(
                    format,
                    input_path,
                    module_path,
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

    /// Initializes a workspace database with all inputs set.
    ///
    /// This is the primary entry point for setting up the query database.
    /// It runs workspace discovery, sets up inputs, and returns the initialized
    /// database with the entry file ID.
    ///
    /// Use queries to get derived data:
    /// - `workspace_diagnostics(&db, ())` for all errors
    /// - `workspace_source_map(&db, ())` for combined source map
    pub fn init_workspace(
        &self,
        options: &BuildOptions,
        overlays: Option<HashMap<FilePath, String>>,
    ) -> Result<WorkspaceResult, Vec<RayError>> {
        // Build search paths for library resolution
        let mut search_paths = vec![self.ray_paths.get_lib_path()];
        if let Some(link_paths) = &options.link_modules {
            search_paths.extend(link_paths.iter().cloned());
        }

        // Create database (with disk cache if workspace root is known)
        let db = if let Some(ref ws_root) = self.workspace_root {
            let cache_dir = ws_root.join(".ray").join("cache");
            log::info!(
                "[init_workspace] disk cache enabled at {}",
                cache_dir.display()
            );
            Database::with_disk_cache(cache_dir)
        } else {
            Database::new()
        };

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

        // Get entry file
        let entry_file = workspace.entry.ok_or_else(|| {
            vec![RayError {
                msg: "no entry file in workspace".to_string(),
                src: vec![],
                kind: RayErrorKind::Compile,
                context: None,
            }]
        })?;

        // Set the workspace as input
        db.set_input::<WorkspaceSnapshot>((), workspace);

        // Set loaded libraries as input
        db.set_input::<LoadedLibraries>((), loaded_libs);

        if options.print_ast {
            let workspace = db.get_input::<WorkspaceSnapshot>(());
            for fid in workspace.all_file_ids() {
                let file_ast_result = file_ast(&db, fid);
                for decl in &file_ast_result.ast.decls {
                    eprintln!("{}", decl);
                }
            }
        }

        log::debug!("[init_workspace] Workspace initialized");
        log::debug!("[init_workspace] entry_file: {:?}", entry_file);

        Ok(WorkspaceResult { db, entry_file })
    }

    /// Legacy method for backward compatibility.
    ///
    /// Prefer using `init_workspace()` and queries instead.
    #[deprecated(note = "Use init_workspace() and queries instead")]
    #[allow(deprecated)]
    pub fn build_frontend(
        &self,
        options: &BuildOptions,
        overlays: Option<HashMap<FilePath, String>>,
    ) -> Result<FrontendResult, Vec<RayError>> {
        let result = self.init_workspace(options, overlays)?;

        let module_path = result.entry_module_path();
        let paths = result.module_paths();

        // Eagerly collect errors and source map for backward compatibility
        let errors = workspace_diagnostics(&result.db, ());
        let srcmap = workspace_source_map(&result.db, ());

        Ok(FrontendResult {
            db: result.db,
            file_id: result.entry_file,
            module_path,
            srcmap,
            paths,
            errors,
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
        let workspace = self.init_workspace(&options, None)?;

        // Check for errors using the query
        let errors = workspace_diagnostics(&workspace.db, ());
        workspace.db.dump_stats();

        // Flush cache regardless of errors — individual query results are
        // still valid and will speed up the next build.
        if let Err(e) = workspace.db.flush_cache() {
            log::warn!("failed to flush cache: {}", e);
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        if options.no_compile {
            return Ok(());
        }

        let db = &workspace.db;
        let module_path = workspace.entry_module_path();
        let module_paths = workspace.module_paths();
        let srcmap = workspace_source_map(db, ());

        let mut program = lir::generate(db, options.build_lib)?;
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

            let module_paths_vec = modules
                .into_iter()
                .map(|p| ModulePath::from(p.to_string().as_str()))
                .collect();
            let lib_data = build_library_data(db, module_paths_vec, srcmap.clone());
            log::debug!(
                "library data: names={} schemes={} structs={} traits={} impls={}",
                lib_data.names.len(),
                lib_data.schemes.len(),
                lib_data.structs.len(),
                lib_data.traits.len(),
                lib_data.impls.len(),
            );
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
