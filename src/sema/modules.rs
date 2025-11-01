use top::{Subst, Substitutable, TyVar as TopTyVar, solver::SolveResult};

use crate::{
    ast::{self, Decl, Expr, Import, Module, Path},
    collections::nametree::Scope,
    driver::RayPaths,
    errors::{RayError, RayErrorKind, RayResult},
    libgen::RayLib,
    lir::Program,
    parse::{self, ParseOptions, Parser},
    pathlib::FilePath,
    span::{Source, SourceMap, Span},
    strutils, transform,
    typing::{
        TyCtx,
        info::TypeSystemInfo,
        state::{Env, SchemeEnv},
        ty::{Ty, TyScheme, TyVar},
    },
};

use std::{
    collections::{HashMap, HashSet},
    fs,
};

use super::NameContext;

const C_STANDARD_INCLUDE_PATHS: [&'static str; 2] = ["/usr/include", "/usr/local/include"];

pub(crate) struct ModBuilderResult {
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
    c_include_paths: Vec<FilePath>,
    paths: &'a RayPaths,
    errors: Vec<RayError>,
    overlays: Option<HashMap<FilePath, String>>,
}

impl<'a> ModuleBuilder<'a, Expr, Decl> {
    pub(crate) fn new(paths: &'a RayPaths, c_include_paths: Vec<FilePath>, no_core: bool) -> Self {
        ModuleBuilder {
            paths,
            c_include_paths,
            no_core,
            modules: HashMap::new(),
            srcmaps: HashMap::new(),
            libs: HashMap::new(),
            ncx: NameContext::new(),
            module_paths: HashSet::new(),
            errors: Vec::new(),
            overlays: None,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn from_src(
        src: &str,
        module_path: ast::Path,
    ) -> Result<ModBuilderResult, Vec<RayError>> {
        let paths = RayPaths::default();
        let mut builder = ModuleBuilder::new(&paths, vec![], true);
        let scope = builder.build_from_src(src.to_string(), module_path)?;
        builder.finish(&scope.path)
    }

    pub fn take_errors(self) -> Vec<RayError> {
        self.errors
    }

    pub(crate) fn finish(self, module_path: &ast::Path) -> Result<ModBuilderResult, Vec<RayError>> {
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

    fn build(
        &mut self,
        mut root_file: ast::File,
        mut srcmap: SourceMap,
        root_fp: &FilePath,
        input_path: &FilePath,
        module_path: ast::Path,
    ) -> Result<Scope, RayError> {
        let mut filepaths = vec![root_fp.clone()];
        let mut submodules = vec![];
        let mut stmts = root_file.stmts.drain(..).collect::<Vec<_>>();
        let mut decls = root_file.decls.drain(..).collect::<Vec<_>>();

        if input_path.is_dir() {
            let (subfile_paths, submod_paths) =
                self.get_subs(&root_fp, &input_path, &module_path)?;

            // parse each file in the module
            for fp in subfile_paths {
                match self.build_file(&mut srcmap, &fp, &module_path) {
                    Ok(f) => {
                        filepaths.push(fp);
                        stmts.extend(f.stmts);
                        decls.extend(f.decls);
                    }
                    Err(e) => self.errors.push(e),
                }
            }

            // collect submodules
            for (f, m) in submod_paths {
                match self.build_from_path(&f, Some(m)) {
                    Ok(Some(m)) => submodules.push(m.path),
                    Ok(None) => { /* do nothing */ }
                    Err(e) => self.errors.push(e),
                }
            }
        }

        // collect from imports
        let mut imports = vec![];

        if !self.no_core {
            // first add the core if it hasn't been added already
            self.add_stdlib_import(&module_path, &["core"], &mut imports);
            self.add_stdlib_import(&module_path, &["core", "io"], &mut imports);
        }

        // then build all of the imports from the root file
        let mut c_decl_set = HashSet::new();
        for import in root_file.imports.iter() {
            match self.resolve_import(&root_file.filepath, &module_path, import) {
                // C includes have no module path or named path
                Ok(ResolvedImport {
                    filepath: Some(filepath),
                    ..
                }) if matches!(import.kind, ast::ImportKind::CImport(..)) => {
                    if let Ok(tys) = parse::cparse(&filepath, &self.c_include_paths) {
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
                // handle the regular path imports
                Ok(ResolvedImport {
                    filepath: Some(filepath),
                    module_path: Some(import_module_path),
                    named_path,
                }) => match &import.kind {
                    ast::ImportKind::Path(_) | ast::ImportKind::Names(_, _) => {
                        self.add_import(&module_path, &import_module_path);
                        match self.build_from_path(&filepath, Some(import_module_path)) {
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
                                                    .names
                                                    .get_or_insert_with(|| HashSet::new())
                                                    .insert(path.to_string());
                                            }
                                        }
                                    }
                                    ast::ImportKind::Names(_, names) => {
                                        scope
                                            .names
                                            .get_or_insert_with(|| HashSet::new())
                                            .extend(names.iter().map(|n| n.to_string()));
                                    }
                                    ast::ImportKind::CImport(..) => unreachable!(),
                                }
                                imports.push(scope)
                            }
                            Err(err) => self.errors.push(err),
                            Ok(None) => continue,
                        }
                    }
                    ast::ImportKind::CImport(..) => unreachable!(),
                },
                Err(err) => self.errors.push(err),
                _ => continue,
            }
        }

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
    ) -> Result<Scope, RayError> {
        // check if module has already been built
        if self.module_paths.contains(&module_path) {
            return Ok(module_path.into());
        }

        self.module_paths.insert(module_path.clone());

        let mut srcmap = SourceMap::new();
        let root_file = Parser::parse_from_src(
            &src,
            ParseOptions {
                filepath: FilePath::new(),
                original_filepath: FilePath::new(),
                module_path: module_path.clone(),
                use_stdin: false,
            },
            &mut srcmap,
        )?;

        // the "filepath"
        let fpath = FilePath::new();
        self.build(root_file, srcmap, &fpath, &fpath, module_path)
    }

    pub fn build_from_path(
        &mut self,
        input_path: &FilePath,
        module_path: Option<ast::Path>,
    ) -> Result<Option<Scope>, RayError> {
        log::debug!(
            "build from path: {} (module_path = {:?})",
            input_path,
            module_path
        );
        let root_fp = match self.get_root_module(input_path, &module_path)? {
            Some(fp) => fp,
            None => return Ok(None),
        };

        let module_path = module_path.unwrap_or_else(|| ast::Path::from(input_path.clone()));

        // check if module has already been built
        if self.module_paths.contains(&module_path) {
            return Ok(Some(module_path.into()));
        }

        self.module_paths.insert(module_path.clone());

        // the library file can be used instead
        if root_fp.has_extension("raylib") || root_fp.file_name() == ".raylib" {
            self.load_library(root_fp, &module_path)?;
            return Ok(Some(module_path.into()));
        }

        let mut srcmap = SourceMap::new();
        let root_file = self.build_file(&mut srcmap, &root_fp, &module_path)?;
        Ok(Some(self.build(
            root_file,
            srcmap,
            &root_fp,
            input_path,
            module_path,
        )?))
    }

    pub fn build_from_path_with_overlay(
        &mut self,
        input_path: &FilePath,
        module_path: Option<ast::Path>,
        overlays: Option<HashMap<FilePath, String>>,
    ) -> Result<Option<Scope>, RayError> {
        let prev = if let Some(overlays) = overlays {
            self.overlays.replace(overlays)
        } else {
            None
        };
        let result = self.build_from_path(input_path, module_path);
        self.overlays = prev;
        result
    }

    fn build_file(
        &mut self,
        srcmap: &mut SourceMap,
        input_path: &FilePath,
        module_path: &ast::Path,
    ) -> Result<ast::File, RayError> {
        if let Some(src) = self.overlays.as_ref().and_then(|o| o.get(input_path)) {
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
        }
    }

    fn add_stdlib_import<I, P>(
        &mut self,
        module_path: &ast::Path,
        path: I,
        imports: &mut Vec<Scope>,
    ) where
        I: IntoIterator<Item = P>,
        P: AsRef<str>,
    {
        let core_path = ast::Path::from(
            path.into_iter()
                .map(|p| p.as_ref().to_string())
                .collect::<Vec<_>>(),
        );

        if !self.module_paths.contains(&core_path) {
            self.add_import(module_path, &core_path);
            let input_path = &self.paths.get_lib_path() / core_path.to_filepath();
            match self.build_from_path(&input_path, Some(core_path)) {
                Ok(Some(scope)) => imports.push(scope),
                Ok(None) => { /* do nothing */ }
                Err(err) => self.errors.push(err),
            }
        }
    }

    fn add_import(&mut self, path: &ast::Path, import: &ast::Path) {
        match self.ncx.imports_mut().get_mut(path) {
            Some(imports) => {
                if !imports.contains(import) {
                    imports.push(import.clone());
                }
            }
            None => {
                let imports = vec![import.clone()];
                self.ncx.imports_mut().insert(path.clone(), imports);
            }
        }
    }

    pub fn get_root_module(
        &mut self,
        path: &FilePath,
        module_path: &Option<ast::Path>,
    ) -> Result<Option<FilePath>, RayError> {
        // first if not an entrypoint, check if there's a
        // pre-built .raylib in the build cache on disk
        let is_entrypoint = module_path.is_none();
        if let Some(module_path) = module_path {
            let build_path = self.paths.get_build_path();
            log::debug!("build_path: {}", build_path);
            let lib_path = (build_path / module_path.join("#")).with_extension("raylib");
            log::debug!("lib_path: {}", lib_path);
            if lib_path.exists() {
                log::debug!("found lib: {}", lib_path);
                return Ok(Some(lib_path));
            }
        }

        if self
            .overlays
            .as_ref()
            .map(|o| o.contains_key(path))
            .unwrap_or_default()
        {
            return Ok(Some(path.clone()));
        }

        if path.exists() && !path.is_dir() {
            return Ok(Some(path.clone()));
        }

        if path.is_dir() {
            // we found a directory matching the name of the module
            // let's look for a .raylib, mod.ray, module.ray, or BASE.ray file
            // note: .raylib must be first
            let base = path.canonicalize()?.file_name();
            for name in [".raylib", "module.ray", "mod.ray", &format!("{}.ray", base)].iter() {
                if *name == ".raylib" && is_entrypoint {
                    // we want to ignore .raylib in the case that we're building
                    // the module that is contained in the .raylib itself
                    continue;
                }

                let fp = path / name;
                if fp.exists() {
                    return Ok(Some(fp));
                }
            }

            self.errors.push(RayError {
                msg: format!(
                    "No root module file. mod.ray, module.ray, or {base}.ray should exist in the directory {path}",
                    base=base, path=path
                ),
                src: vec![Source {
                    filepath: path.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
                context: Some("root module resolution".to_string()),
            });
        } else {
            self.errors.push(RayError {
                msg: format!("{} does not exist or is not a directory", path),
                src: vec![Source {
                    filepath: path.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::IO,
                context: Some("root module resolution".to_string()),
            });
        }

        Ok(None)
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
    ) -> Result<ResolvedImport, RayError> {
        log::debug!("resolve import from {}: {}", parent_filepath, import);
        match &import.kind {
            ast::ImportKind::Path(path) => {
                self.resolve_path_import(path, parent_filepath, parent_module_path, &import.span)
            }
            ast::ImportKind::Names(path, _) => {
                let filepath =
                    match self.resolve_module_import(path, parent_filepath, &import.span)? {
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
    ) -> Result<ResolvedImport, RayError> {
        // the path can either be a path to a module or name within a module
        // first, check if the path is a module path
        match self.resolve_module_import(path, parent_filepath, span) {
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
        if let Some(filepath) = self.resolve_module_import(&parent_path, parent_filepath, span)? {
            // we found a module and now we need to see if we can find a name in the module
            let path = parent_module_path.append_path(path.clone()).canonicalize();
            let (parent_module_path, module_path) =
                parent_path.resolve_from_parent(parent_module_path);
            let module_path = parent_module_path.append_path(module_path);
            log::debug!("resolved path import: {} => {}", path, module_path);
            match self.build_from_path(&filepath, Some(module_path.clone())) {
                Ok(_) => {
                    return Ok(ResolvedImport {
                        filepath: Some(filepath),
                        module_path: Some(module_path),
                        named_path: Some(path),
                    });
                }
                Err(e) => self.errors.push(e),
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
    ) -> Result<Option<FilePath>, RayError> {
        log::debug!("resolve module import from {}: {}", parent_filepath, path);

        let curr_dirpath = if parent_filepath.is_dir() {
            parent_filepath.clone()
        } else {
            parent_filepath.dir()
        };

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
                possible_paths.push(filepath);
                continue;
            }

            // check if module directory exists
            if dirpath.is_dir() {
                // we found a directory matching the name of the module
                // let's look for a module.ray or BASE.ray file
                let mut filepath = &dirpath / "module.ray";
                if !filepath.exists() {
                    let base = &format!("{}.ray", path.name().unwrap());
                    filepath = &dirpath / base;
                    if !filepath.exists() {
                        // no "root" module file
                        let dirbase = dirpath.file_name();
                        return Err(RayError {
                            msg: format!(
                                "Root module file does not exist. Either {dirbase}/module.ray or {dirbase}/{base} is required.",
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

                if self.is_submodule(&parent_filepath, &filepath) {
                    submodule_paths.push(filepath);
                } else {
                    possible_paths.push(filepath);
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

    fn get_subs(
        &mut self,
        root_fp: &FilePath,
        module_dir: &FilePath,
        mod_path: &ast::Path,
    ) -> Result<(Vec<FilePath>, Vec<(FilePath, ast::Path)>), RayError> {
        let mut submods = vec![];
        let mut subfiles = vec![];
        let dir = module_dir.read_dir()?;
        for r in dir {
            let entry = r?;
            let fp = FilePath::from(entry.path());
            if &fp != root_fp {
                if self.is_dir_module(&fp) {
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

    // fn is_module(&self, path: &Path, parent_filepath: &FilePath) -> bool {
    //     let curr_dirpath = if parent_filepath.is_dir() {
    //         parent_filepath.clone()
    //     } else {
    //         parent_filepath.dir()
    //     };

    //     let stdlib_path = self.paths.get_stdlib_path();
    //     let paths_to_check = vec![&stdlib_path, &curr_dirpath];
    // }

    fn is_dir_module(&self, dir: &FilePath) -> bool {
        if !dir.is_dir() {
            return false;
        }
        let entries = match dir.read_dir() {
            Ok(entries) => entries,
            Err(_) => return false,
        };
        for r in entries {
            if let Ok(entry) = r {
                if FilePath::from(entry.path()).has_extension("ray") {
                    // as long as we have at least one ".ray" file, then this is a module
                    return true;
                }
            }
        }

        return false;
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
        self.tcx.apply_subst(&solution.subst);
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
