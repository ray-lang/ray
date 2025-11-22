use std::{
    collections::{HashMap, HashSet},
    fs,
};

use top::{Subst, Substitutable, TyVar as TopTyVar, solver::SolveResult};

use crate::{
    ast::{self, Decl, Expr, Import, Module, Path},
    collections::nametree::Scope,
    errors::{RayError, RayErrorKind, RayResult},
    libgen::RayLib,
    lir::Program,
    parse::{self, ParseDiagnostics, ParseOptions, Parser},
    pathlib::{FilePath, RayPaths},
    span::{Source, SourceMap, Span},
    strutils, transform,
    typing::{
        TyCtx,
        info::TypeSystemInfo,
        state::{Env, SchemeEnv},
        ty::{Ty, TyScheme, TyVar},
    },
};

use super::{NameContext, root};

const C_STANDARD_INCLUDE_PATHS: [&'static str; 2] = ["/usr/include", "/usr/local/include"];

pub struct ModBuilderResult {
    pub module: Module<(), Decl>,
    pub tcx: TyCtx,
    pub ncx: NameContext,
    pub srcmap: SourceMap,
    pub defs: SchemeEnv,
    pub libs: Vec<Program>,
    pub paths: HashSet<ast::Path>,
}

#[derive(Debug, Default)]
struct ResolvedImport {
    filepath: Option<FilePath>,
    module_path: Option<ast::Path>,
    named_path: Option<ast::Path>,
}

pub struct BuildInput {
    filepath: FilePath,
    module_path: ast::Path,
    is_entry: bool,
}

impl BuildInput {
    pub fn new(filepath: FilePath, module_path: ast::Path) -> BuildInput {
        BuildInput {
            filepath,
            module_path,
            is_entry: false,
        }
    }

    pub fn entry(filepath: FilePath, module_path: ast::Path) -> BuildInput {
        BuildInput {
            filepath,
            module_path,
            is_entry: true,
        }
    }
}

#[derive(Debug)]
pub struct ModuleBuilder<'a, A, B>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub modules: HashMap<ast::Path, Module<A, B>>,
    pub srcmaps: HashMap<ast::Path, SourceMap>,
    pub libs: HashMap<ast::Path, RayLib>,
    pub ncx: NameContext,
    no_core: bool,
    module_paths: HashSet<ast::Path>,
    top_level_roots: HashMap<ast::Path, FilePath>,
    c_include_paths: Vec<FilePath>,
    paths: &'a RayPaths,
    errors: Vec<RayError>,
    overlays: Option<HashMap<FilePath, String>>,
}

impl<'a> ModuleBuilder<'a, Expr, Decl> {
    pub fn new(paths: &'a RayPaths, c_include_paths: Vec<FilePath>, no_core: bool) -> Self {
        ModuleBuilder {
            paths,
            c_include_paths,
            no_core,
            modules: HashMap::new(),
            srcmaps: HashMap::new(),
            libs: HashMap::new(),
            ncx: NameContext::new(),
            module_paths: HashSet::new(),
            top_level_roots: HashMap::new(),
            errors: Vec::new(),
            overlays: None,
        }
    }

    pub fn from_src(src: &str, module_path: ast::Path) -> Result<ModBuilderResult, Vec<RayError>> {
        let paths = RayPaths::default();
        let mut builder = ModuleBuilder::new(&paths, vec![], true);
        let scope = builder.build_from_src(src.to_string(), module_path)?;
        builder.finish(&scope.path)
    }

    fn is_overlay(&self, path: &FilePath) -> bool {
        self.overlays
            .as_ref()
            .map_or(false, |overlays| overlays.contains_key(path))
    }

    pub fn take_errors(self) -> Vec<RayError> {
        self.errors
    }

    pub fn finish(self, module_path: &ast::Path) -> Result<ModBuilderResult, Vec<RayError>> {
        if !self.errors.is_empty() {
            return Err(self.errors);
        }
        let mut libs = vec![];
        let mut ncx = self.ncx;
        let mut srcmaps = self.srcmaps;
        let mut lib_set = HashSet::new();
        let mut defs = Env::new();
        let mut tcx = TyCtx::new();
        let mut definitions = HashMap::new();
        for (lib_path, mut lib) in self.libs {
            // create a substitution to map the library's variables
            let subst = (0..lib.tcx.tf().curr())
                .flat_map(|u| {
                    let old_var = TyVar::from_u32(u as u32);
                    if u == tcx.tf().curr() {
                        // generate and ignore the new variable
                        let _ = tcx.tf().next();
                        return None;
                    }
                    let new_var = tcx.tf().next();
                    Some((old_var, Ty::Var(new_var)))
                })
                .collect::<Subst<TyVar, Ty>>();
            log::debug!("subst: {}", subst);
            lib.tcx.apply_subst_all(&subst);
            lib.program.apply_subst_all(&subst);

            lib_set.insert(lib_path.clone());
            tcx.extend(lib.tcx);
            ncx.extend(lib.ncx);
            srcmaps.insert(lib_path, lib.srcmap);
            libs.push(lib.program);
            defs.extend(lib.defs);
            definitions.extend(lib.definitions.into_iter());
        }

        let modules = self.modules;
        let paths = modules.iter().map(|(p, _)| p.clone()).collect();
        log::debug!("paths: {:?}", paths);
        let (module, srcmap, tcx, ncx) =
            match transform::combine(module_path, modules, srcmaps, lib_set, tcx, ncx) {
                Ok((module, srcmap, _, tcx, ncx)) => (module, srcmap, tcx, ncx),
                Err(errs) => {
                    return Err(errs);
                }
            };

        Ok(ModBuilderResult {
            module,
            tcx,
            ncx,
            srcmap,
            defs,
            libs,
            paths,
        })
    }

    /// This is the entrypoint for the module builder
    pub fn build(
        &mut self,
        input_path: &FilePath,
        overlays: Option<HashMap<FilePath, String>>,
    ) -> Result<Option<Scope>, Vec<RayError>> {
        let prev = if let Some(overlays) = overlays {
            self.overlays.replace(overlays)
        } else {
            None
        };

        // here we need to determine the module path based on the input filepath
        let module_path = self.resolve_module_path(input_path);
        log::debug!(
            "[ModuleBuilder] resolving module path: {} => {}",
            input_path,
            module_path
        );
        let input = BuildInput::entry(input_path.clone(), module_path);
        let result = self.build_from_path(input);
        self.overlays = prev;
        result
    }

    fn build_from_file(
        &mut self,
        mut root_file: ast::File,
        mut srcmap: SourceMap,
        root_fp: &FilePath,
        module_path: ast::Path,
    ) -> Result<Scope, Vec<RayError>> {
        let mut filepaths = vec![root_fp.clone()];
        let mut submodules = vec![];
        let mut stmts = root_file.stmts.drain(..).collect::<Vec<_>>();
        let mut decls = root_file.decls.drain(..).collect::<Vec<_>>();

        // When building from an in-memory source (e.g. tests via `from_src`), the
        // "filepath" may be empty. In that case, there is no directory root and we
        // must not try to inspect the filesystem for submodules.
        let module_dir = if root_fp.is_empty() {
            root_fp.clone()
        } else {
            root_fp.dir()
        };
        let has_dir_root = !root_fp.is_empty() && root::is_dir_module(&module_dir);
        if has_dir_root {
            self.register_top_level_root(&module_path, &module_dir);
        }
        let module_root = self.lookup_top_level_root(&module_path);

        log::debug!(
            "[build_from_file] root_fp={}, module_dir={}, has_dir_root={}, module_root={:?}",
            root_fp,
            module_dir,
            has_dir_root,
            module_root
        );

        if has_dir_root {
            self.build_submodules(
                root_fp,
                &module_dir,
                &module_path,
                &mut filepaths,
                &mut submodules,
                &mut stmts,
                &mut decls,
                &mut srcmap,
            )?;
        }

        let imports =
            self.build_imports(&root_file, &module_path, &mut decls, module_root.as_ref());

        self.srcmaps.insert(module_path.clone(), srcmap);
        self.modules.insert(
            module_path.clone(),
            Module {
                submodules,
                imports,
                import_stmts: root_file.imports,
                stmts,
                decls,
                filepaths,
                defs: Env::new(),
                path: module_path.clone(),
                root_filepath: root_file.filepath,
                doc_comment: root_file.doc_comment,
                is_lib: false,
            },
        );
        Ok(module_path.into())
    }

    pub fn build_from_src(
        &mut self,
        src: String,
        module_path: ast::Path,
    ) -> Result<Scope, Vec<RayError>> {
        // check if module has already been built
        if self.module_paths.contains(&module_path) {
            return Ok(module_path.into());
        }

        self.module_paths.insert(module_path.clone());

        let mut srcmap = SourceMap::new();
        let root_file = match Parser::parse_from_src(
            &src,
            ParseOptions {
                filepath: FilePath::new(),
                original_filepath: FilePath::new(),
                module_path: module_path.clone(),
                use_stdin: false,
            },
            &mut srcmap,
        ) {
            ParseDiagnostics {
                value: Some(file),
                errors,
            } if errors.is_empty() => file,
            ParseDiagnostics { value: _, errors } => return Err(errors),
        };

        // the "filepath"
        let fpath = FilePath::new();
        self.build_from_file(root_file, srcmap, &fpath, module_path)
    }

    pub fn build_from_path(&mut self, input: BuildInput) -> Result<Option<Scope>, Vec<RayError>> {
        log::debug!(
            "build from path: {} (module_path = {:?})",
            input.filepath,
            input.module_path
        );
        let module_filepath = match self.get_module_filepath(&input)? {
            Some(fp) => fp,
            None => return Ok(None),
        };

        log::debug!(
            "[build_from_path] filepath={}, module_path={}, is_entry={}, module_filepath={}",
            input.filepath,
            input.module_path,
            input.is_entry,
            module_filepath
        );

        // check if module has already been built
        if self.module_paths.contains(&input.module_path) {
            log::debug!(
                "[build_from_path] module already built: {}",
                input.module_path
            );
            return Ok(Some(input.module_path.into()));
        }

        self.module_paths.insert(input.module_path.clone());

        // the library file can be used instead
        if module_filepath.has_extension("raylib") || module_filepath.file_name() == ".raylib" {
            self.load_library(module_filepath, &input.module_path)?;
            return Ok(Some(input.module_path.into()));
        }

        let mut srcmap = SourceMap::new();
        let file = self.parse_file(&mut srcmap, &module_filepath, &input.module_path)?;
        Ok(Some(self.build_from_file(
            file,
            srcmap,
            &module_filepath,
            input.module_path,
        )?))
    }

    fn parse_file(
        &self,
        srcmap: &mut SourceMap,
        input_path: &FilePath,
        module_path: &ast::Path,
    ) -> Result<ast::File, Vec<RayError>> {
        let diag = if let Some(src) = self.overlays.as_ref().and_then(|o| o.get(input_path)) {
            log::info!("parsing {} (overlay)", input_path);
            Parser::parse_from_src(
                src,
                ParseOptions {
                    filepath: input_path.clone(),
                    original_filepath: input_path.clone(),
                    module_path: module_path.clone(),
                    use_stdin: false,
                },
                srcmap,
            )
        } else {
            log::info!("parsing {}", input_path);
            Parser::parse(
                ParseOptions {
                    filepath: input_path.clone(),
                    original_filepath: input_path.clone(),
                    module_path: module_path.clone(),
                    use_stdin: false,
                },
                srcmap,
            )
        };

        diag.into()
    }

    fn inject_import<I, P>(&mut self, path: I, imports: &mut Vec<Scope>)
    where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
    {
        let core_path = ast::Path::from(
            path.into_iter()
                .map(|p| p.as_ref().to_string())
                .collect::<Vec<_>>(),
        );

        if !self.module_paths.contains(&core_path) {
            let core_fp = &self.paths.get_lib_path() / core_path.to_filepath();
            let input_path = core_fp.canonicalize().unwrap_or(core_fp.clone());
            let input = BuildInput::new(input_path, core_path);
            match self.build_from_path(input) {
                Ok(Some(scope)) => imports.push(scope),
                Ok(None) => { /* do nothing */ }
                Err(err) => self.errors.extend(err),
            }
        }
    }

    fn build_imports(
        &mut self,
        root_file: &ast::File,
        module_path: &ast::Path,
        decls: &mut Vec<ast::Node<ast::Decl>>,
        module_root: Option<&FilePath>,
    ) -> Vec<Scope> {
        let mut imports = vec![];

        if !self.no_core {
            // first add the core if it hasn't been added already
            self.inject_import(&["core"], &mut imports);
            self.inject_import(&["core", "io"], &mut imports);
        }

        // then build all of the imports from the root file
        let mut c_decl_set = HashSet::new();
        for import in root_file.imports.iter() {
            match self.resolve_import(&root_file.filepath, &module_path, import, module_root) {
                // C includes have no module path or named path
                Ok(ResolvedImport {
                    filepath: Some(filepath),
                    ..
                }) if matches!(import.kind, ast::ImportKind::CImport(..)) => {
                    self.build_c_import(&filepath, decls, &mut c_decl_set)
                }
                // handle the regular path imports
                Ok(ResolvedImport {
                    filepath: Some(filepath),
                    module_path: Some(import_module_path),
                    named_path,
                }) => match &import.kind {
                    ast::ImportKind::Path(_) | ast::ImportKind::Names(_, _) => self.build_import(
                        import,
                        &filepath,
                        import_module_path,
                        named_path,
                        &mut imports,
                    ),
                    ast::ImportKind::CImport(..) => unreachable!(),
                },
                Err(err) => self.errors.push(err),
                _ => continue,
            }
        }

        imports
    }

    fn register_top_level_root(&mut self, module_path: &ast::Path, module_dir: &FilePath) {
        let root_path = match module_path.root() {
            Some(root) => root,
            None => return,
        };

        if self.top_level_roots.contains_key(&root_path) {
            return;
        }

        let mut top_dir = module_dir.clone();
        let depth = module_path.len().saturating_sub(1);
        for _ in 0..depth {
            if let Some(parent) = top_dir.parent_dir() {
                top_dir = parent;
            } else {
                break;
            }
        }

        let canonical = top_dir.canonicalize().unwrap_or(top_dir.clone());
        self.top_level_roots.insert(root_path, canonical);
    }

    fn lookup_top_level_root(&self, module_path: &ast::Path) -> Option<FilePath> {
        let key = module_path.root()?;
        self.top_level_roots.get(&key).cloned()
    }

    fn build_submodules(
        &mut self,
        root_fp: &FilePath,
        input_path: &FilePath,
        module_path: &ast::Path,
        filepaths: &mut Vec<FilePath>,
        submodules: &mut Vec<ast::Path>,
        stmts: &mut Vec<ast::Node<ast::Expr>>,
        decls: &mut Vec<ast::Node<ast::Decl>>,
        srcmap: &mut SourceMap,
    ) -> RayResult<()> {
        let (subfile_paths, submod_paths) = self.get_subs(&root_fp, &input_path, &module_path)?;

        // parse each file in the module
        for fp in subfile_paths {
            match self.parse_file(srcmap, &fp, &module_path) {
                Ok(f) => {
                    filepaths.push(fp);
                    stmts.extend(f.stmts);
                    decls.extend(f.decls);
                }
                Err(e) => self.errors.extend(e),
            }
        }

        // collect submodules
        for (f, m) in submod_paths {
            let input = BuildInput::new(f, m);
            match self.build_from_path(input) {
                Ok(Some(m)) => submodules.push(m.path),
                Ok(None) => { /* do nothing */ }
                Err(e) => self.errors.extend(e),
            }
        }

        Ok(())
    }

    fn build_import(
        &mut self,
        import: &Import,
        filepath: &FilePath,
        import_module_path: ast::Path,
        named_path: Option<ast::Path>,
        imports: &mut Vec<Scope>,
    ) {
        let input = BuildInput::new(filepath.clone(), import_module_path);
        match self.build_from_path(input) {
            Ok(Some(mut scope)) => {
                match &import.kind {
                    ast::ImportKind::Path(_) => {
                        // check if the resolved path is of the form: MODULE_PATH::NAME
                        if let Some(named_path) = named_path {
                            let path = named_path.without_parent(&scope.path);
                            log::debug!("import module path: {}", scope.path);
                            log::debug!("named path: {}", path);
                            if path != scope.path {
                                // add the NAME to the scope
                                scope
                                    .whitelist
                                    .get_or_insert_with(|| HashSet::new())
                                    .insert(path.to_string());
                            }
                        }
                    }
                    ast::ImportKind::Names(_, names) => {
                        scope
                            .whitelist
                            .get_or_insert_with(|| HashSet::new())
                            .extend(names.iter().map(|n| n.to_string()));
                    }
                    ast::ImportKind::CImport(..) => unreachable!(),
                }
                imports.push(scope)
            }
            Err(err) => self.errors.extend(err),
            Ok(None) => {}
        }
    }

    fn build_c_import(
        &mut self,
        filepath: &FilePath,
        decls: &mut Vec<ast::Node<ast::Decl>>,
        c_decl_set: &mut HashSet<String>,
    ) {
        if let Ok(tys) = parse::cparse(filepath, &self.c_include_paths) {
            for (ty, span) in tys {
                let decl = ty.convert_to_decl(span);
                let key = decl.to_string();
                if !c_decl_set.contains(&key) {
                    decls.push(decl);
                    c_decl_set.insert(key);
                }
            }
        }
    }

    pub fn get_module_filepath(
        &mut self,
        input: &BuildInput,
    ) -> Result<Option<FilePath>, RayError> {
        let path = &input.filepath;

        if path.is_dir() {
            return self.get_module_filepath_for_dir(input);
        }

        if path.exists() {
            return Ok(Some(root::module_entry_path(path)));
        }

        // If this path is provided via an in-memory overlay (e.g. tests) but does
        // not exist on disk, treat it as a valid module input.
        if self.is_overlay(path) {
            return Ok(Some(path.clone()));
        }

        // If the provided path does not exist, attempt to resolve by cached artifact with the module path.
        if let Some(lib_path) = self.resolve_library(&input.module_path) {
            return Ok(Some(lib_path));
        }

        self.errors.push(RayError {
            msg: format!("{} does not exist or is not a directory", path),
            src: vec![Source {
                filepath: path.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::IO,
            context: Some("root module resolution".to_string()),
        });

        Ok(None)
    }

    fn get_module_filepath_for_dir(
        &mut self,
        input: &BuildInput,
    ) -> Result<Option<FilePath>, RayError> {
        // We found a directory that could be a module.
        // RFC rule: prefer source if present; only fall back to a local .raylib when no source file exists.
        let path = &input.filepath;
        let base = path.canonicalize()?.file_name();

        // 1) Prefer source entry files inside the directory.
        for name in ["mod.ray", &format!("{}.ray", base)].iter() {
            let fp = path / name;
            if fp.exists() {
                return Ok(Some(fp));
            }
        }

        // 2) If no source files, allow a *local* .raylib only when we are not treating this directory
        //    as the implicit entrypoint (i.e., when module_path is Some). For entrypoints, ignore local .raylib.
        let local_lib = path / ".raylib";
        if local_lib.exists() && !input.is_entry {
            return Ok(Some(local_lib));
        }

        // 3) Final fallback: try cached artifacts in build/lib roots from the module path.
        if let Some(lib_path) = self.resolve_library(&input.module_path) {
            return Ok(Some(lib_path));
        }

        self.errors.push(RayError {
            msg: format!(
                "No root module file. mod.ray or {base}.ray should exist in the directory {path}",
            ),
            src: vec![Source {
                filepath: path.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Import,
            context: Some("root module resolution".to_string()),
        });

        Ok(None)
    }

    fn resolve_library(&self, module_path: &ast::Path) -> Option<FilePath> {
        let roots = [self.paths.get_lib_path()];
        for root in roots {
            let lib_path = (root / module_path.join("#")).with_extension("raylib");
            log::debug!("lib_path: {}", lib_path);
            if lib_path.exists() {
                log::debug!("found lib: {}", lib_path);
                return Some(lib_path);
            }
        }

        None
    }

    fn load_library(&mut self, lib_path: FilePath, module_path: &ast::Path) -> RayResult<()> {
        if self.libs.contains_key(module_path) {
            // already loaded
            log::debug!("library already loaded: {}", module_path);
            return Ok(());
        }

        let lib: RayLib = match bincode::deserialize_from(fs::File::open(&lib_path)?) {
            Ok(l) => l,
            Err(e) => {
                return Err(RayError {
                    msg: format!("Failed loading library file {}: {}", lib_path, e),
                    src: vec![Source {
                        filepath: lib_path,
                        ..Default::default()
                    }],
                    kind: RayErrorKind::Parse,
                    context: Some("loading raylib file".to_string()),
                });
            }
        };

        // add each library module to the list of input paths
        for path in lib.modules.iter().cloned() {
            self.module_paths.insert(path);
        }

        self.libs.insert(module_path.clone(), lib);
        Ok(())
    }

    fn resolve_import(
        &mut self,
        parent_filepath: &FilePath,
        parent_module_path: &ast::Path,
        import: &Import,
        module_root: Option<&FilePath>,
    ) -> Result<ResolvedImport, RayError> {
        log::debug!("resolve import from {}: {}", parent_filepath, import);
        match &import.kind {
            ast::ImportKind::Path(path) => self.resolve_path_import(
                path,
                parent_filepath,
                parent_module_path,
                &import.span,
                module_root,
            ),
            ast::ImportKind::Names(path, _) => {
                let filepath = match self.resolve_module_import(
                    path,
                    parent_filepath,
                    &import.span,
                    module_root,
                )? {
                    Some(fp) => fp,
                    None => return Ok(ResolvedImport::default()),
                };

                let module_path = parent_module_path.append_path(&path.value.clone());
                log::debug!("resolved path import: {}", module_path);
                Ok(ResolvedImport {
                    filepath: Some(filepath),
                    module_path: Some(module_path),
                    named_path: None,
                })
            }
            ast::ImportKind::CImport(include, span) => {
                let filepath = self.resolve_c_include(include, parent_filepath, *span);
                Ok(ResolvedImport {
                    filepath,
                    ..Default::default()
                })
            }
        }
    }

    fn resolve_c_include(
        &mut self,
        include: &str,
        src_path: &FilePath,
        span: Span,
    ) -> Option<FilePath> {
        let mut include_paths = vec![];

        // add the includes from the build options
        include_paths.extend(self.c_include_paths.clone());

        // add the standard include paths
        include_paths.extend(C_STANDARD_INCLUDE_PATHS.iter().map(FilePath::from));

        for p in include_paths {
            let fp = p / include;
            if fp.exists() {
                return Some(fp);
            }
        }

        self.errors.push(RayError {
            kind: RayErrorKind::Import,
            msg: format!("Could not find C header file {:?}", include),
            src: vec![Source {
                filepath: src_path.clone(),
                span: Some(span),
                ..Default::default()
            }],
            context: Some("C include resolution".to_string()),
        });

        None
    }

    fn resolve_path_import(
        &mut self,
        path: &ast::Path,
        parent_filepath: &FilePath,
        parent_module_path: &ast::Path,
        span: &Span,
        module_root: Option<&FilePath>,
    ) -> Result<ResolvedImport, RayError> {
        // the path can either be a path to a module or name within a module
        // first, check if the path is a module path
        match self.resolve_module_import(path, parent_filepath, span, module_root) {
            Ok(Some(filepath)) => {
                let module_path = parent_module_path.append_path(path);
                log::debug!("resolved path import: {}", module_path);
                return Ok(ResolvedImport {
                    filepath: Some(filepath),
                    module_path: Some(module_path),
                    named_path: None,
                });
            }
            _ => { /* fallthrough */ }
        }

        // otherwise, we assume that the path is a module path + name, so we
        // try to find a module that contains the name
        // get the parent path and try to resolve that as a module
        let parent_path = path.parent();
        if let Some(filepath) =
            self.resolve_module_import(&parent_path, parent_filepath, span, module_root)?
        {
            // we found a module and now we need to see if we can find a name in the module
            let path = parent_module_path.append_path(path.clone()).canonicalize();
            let (parent_module_path, module_path) =
                parent_path.resolve_from_parent(parent_module_path);
            let module_path = parent_module_path.append_path(module_path);
            log::debug!("resolved path import: {} => {}", path, module_path);
            let input = BuildInput::new(filepath.clone(), module_path.clone());
            match self.build_from_path(input) {
                Ok(_) => {
                    return Ok(ResolvedImport {
                        filepath: Some(filepath),
                        module_path: Some(module_path),
                        named_path: Some(path),
                    });
                }
                Err(e) => self.errors.extend(e),
            }
        } else {
            // we couldn't find a module based on the path
            self.errors.push(RayError {
                msg: format!("Could not find module from import {}", path),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span: Some(*span),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("module import resolution".to_string()),
            });
        }

        Ok(ResolvedImport::default())
    }

    fn resolve_module_import(
        &self,
        path: &ast::Path,
        parent_filepath: &FilePath,
        span: &Span,
        module_root: Option<&FilePath>,
    ) -> Result<Option<FilePath>, RayError> {
        log::debug!("resolve module import from {}: {}", parent_filepath, path);

        if module_root.is_none() && path.is_relative() {
            return Err(RayError {
                msg: format!(
                    "Cannot use `super` imports in single-file module when resolving {}",
                    path
                ),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span: Some(*span),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("module import resolution".to_string()),
            });
        }

        // `dir` clones the path if already a directory, otherwise returns the parent (directory) path
        let curr_dirpath = parent_filepath.dir();

        // the module could be in the library path or in the current directory
        let mut paths_to_check = vec![curr_dirpath];
        if !path.is_relative() {
            let lib_path = self.paths.get_lib_path();
            paths_to_check.push(lib_path);
        }

        // iterate through the possible paths and check if the module exists
        let mut possible_paths = vec![];
        let mut submodule_paths = vec![];

        // note: `to_filepath` will convert a relative module path to a relative filepath
        let module_fp = &path.to_filepath();
        for possible_path in paths_to_check {
            let dirpath = possible_path / module_fp;
            let filepath = dirpath.with_extension("ray");
            // TODO: ensure that if the filepath is relative it doesn't go outside the root module
            if filepath.exists() {
                let canonical = filepath.canonicalize().unwrap_or(filepath.clone());
                self.ensure_within_root(&canonical, module_root, path, parent_filepath, span)?;
                possible_paths.push(canonical);
                continue;
            }

            // check if module directory exists
            if dirpath.is_dir() {
                // we found a directory matching the name of the module
                // let's look for a mod.ray or <base>.ray file
                let mut filepath = &dirpath / "mod.ray";
                if !filepath.exists() {
                    let base = &format!("{}.ray", path.name().unwrap());
                    filepath = &dirpath / base;
                    if !filepath.exists() {
                        // no "root" module file
                        let dirbase = dirpath.file_name();
                        return Err(RayError {
                            msg: format!(
                                "Root module file does not exist. Either {dirbase}/mod.ray or {dirbase}/{base} is required.",
                            ),
                            src: vec![Source {
                                filepath: parent_filepath.clone(),
                                span: Some(*span),
                                ..Default::default()
                            }],
                            kind: RayErrorKind::Import,
                            context: Some("module import resolution".to_string()),
                        });
                    }
                }

                let canonical = filepath.canonicalize().unwrap_or(filepath.clone());
                self.ensure_within_root(&canonical, module_root, path, parent_filepath, span)?;
                if self.is_submodule(&parent_filepath, &canonical) {
                    submodule_paths.push(canonical);
                } else {
                    possible_paths.push(canonical);
                }
            }
        }

        if possible_paths.len() == 0 && submodule_paths.len() != 0 {
            Err(RayError {
                msg: format!("cannot import a submodule, it is already imported"),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span: Some(*span),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("module import resolution".to_string()),
            })
        } else if possible_paths.len() == 0 {
            Err(RayError {
                msg: format!("Could not find module from import {}", path),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span: Some(*span),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("module import resolution".to_string()),
            })
        } else if possible_paths.len() > 1 {
            Err(RayError {
                msg: format!(
                    "Ambiguous import {}. Found multiple file paths:\n{}",
                    path,
                    strutils::indent_lines_iter(&possible_paths, 2),
                ),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span: Some(*span),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("module import resolution".to_string()),
            })
        } else {
            Ok(Some(possible_paths.pop().unwrap()))
        }
    }

    fn ensure_within_root(
        &self,
        candidate: &FilePath,
        module_root: Option<&FilePath>,
        path: &ast::Path,
        parent_filepath: &FilePath,
        span: &Span,
    ) -> Result<(), RayError> {
        if let Some(root) = module_root {
            let canonical_root = root.canonicalize().unwrap_or(root.clone());
            if !candidate.as_ref().starts_with(canonical_root.as_ref()) {
                return Err(RayError {
                    msg: format!(
                        "Import {} resolves outside the module root {}",
                        path, canonical_root
                    ),
                    src: vec![Source {
                        filepath: parent_filepath.clone(),
                        span: Some(*span),
                        ..Default::default()
                    }],
                    kind: RayErrorKind::Import,
                    context: Some("module import resolution".to_string()),
                });
            }
        }
        Ok(())
    }

    fn get_subs(
        &mut self,
        root_fp: &FilePath,
        module_dir: &FilePath,
        mod_path: &ast::Path,
    ) -> Result<(Vec<FilePath>, Vec<(FilePath, ast::Path)>), RayError> {
        let mut submods = vec![];
        let mut subfiles = vec![];
        let dir = module_dir.read_dir()?;
        for entry in dir.flatten() {
            let fp = FilePath::from(entry.path());
            if &fp != root_fp {
                if root::is_dir_module(&fp) {
                    let base = fp.file_stem();
                    let sub_path = mod_path.append(&base);
                    submods.push((fp, sub_path));
                } else if fp.has_extension("ray") {
                    subfiles.push(fp);
                }
            }
        }

        Ok((subfiles, submods))
    }

    fn resolve_module_path(&self, filepath: &FilePath) -> ast::Path {
        // Single-file module: if this is a file and its *directory* is not a dir-module,
        // treat the file itself as the root module and use its stem.
        if !filepath.is_dir() && !root::is_dir_module(&filepath.dir()) {
            return ast::Path::from(filepath.file_stem());
        }

        // Start from the directory that contains this module: `dir()` clones if already a dir,
        // or returns the parent directory if `filepath` is a file.
        let module_dir = filepath.dir();

        // Walk upward capturing a contiguous chain of module entry directories.
        // A "module directory" is one that contains `mod.ray` or `<basename>.ray`.
        let mut chain: Vec<FilePath> = Vec::new();
        let mut curr = module_dir.clone();
        loop {
            if !root::is_dir_module(&curr) {
                break;
            }
            chain.push(curr.clone());
            match curr.parent_dir() {
                Some(parent) if root::is_dir_module(&parent) => {
                    curr = parent;
                }
                _ => break,
            }
        }

        // If we didn't find any entry dirs, fall back to a single segment: the immediate directory name.
        if chain.is_empty() {
            return ast::Path::from(module_dir.file_name());
        }

        // Build the path from the TOPMOST contiguous entry dir down to `module_dir`.
        let parts: Vec<String> = chain.iter().rev().map(|d| d.file_name()).collect();
        ast::Path::from(parts)
    }

    fn is_submodule(&self, parent_filepath: &FilePath, filepath: &FilePath) -> bool {
        filepath.is_dir() && &filepath.dir() == parent_filepath
    }
}

impl ModBuilderResult {
    pub fn apply_solution(
        &mut self,
        solution: SolveResult<TypeSystemInfo, Ty, TyVar>,
        defs: &SchemeEnv,
    ) {
        let skolem_subst = solution
            .skolems
            .iter()
            .flat_map(|skolem| {
                skolem
                    .vars
                    .iter()
                    .map(|(skolem_var, original)| (skolem_var.clone(), Ty::Var(original.clone())))
            })
            .collect::<Subst<_, _>>();

        self.tcx.apply_subst(&solution.subst);
        self.tcx.apply_subst_all(&skolem_subst);
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
        self.tcx.extend_inst_ty_map(inst_scheme_map);
        let inst_scheme_keys = solution
            .inst_type_schemes
            .keys()
            .cloned()
            .collect::<HashSet<_>>();

        let mut poly_inst_seeds = Subst::<TyVar, TyScheme>::new();
        {
            let tcx = &self.tcx;

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

                    if let Some(scheme) = defs.get(path) {
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
                        log::debug!("poly_inst_seed: no defs entry for {}; skipping", path);
                    }
                }
            };

            for decl in &self.module.decls {
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
            self.tcx.extend_inst_ty_map(poly_inst_seeds);
        }

        log::debug!("defs: {}", defs);

        let filtered_scheme_subst = solution
            .scheme_subst()
            .into_iter()
            .filter_map(|(v, s)| {
                if inst_scheme_keys.contains(&v) {
                    log::debug!("scheme_subst: skipping {} because instantiation exists", v);
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
        self.tcx.extend_scheme_subst(filtered_scheme_subst);
        self.tcx.extend_predicates(solution.qualifiers.clone());
        self.tcx.tf().skip_to(solution.unique as u64);

        log::debug!("{}", self.module);
        log::debug!("{}", self.tcx);
    }
}
