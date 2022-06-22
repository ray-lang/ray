use top::{Subst, Substitutable, TyVar as TopTyVar};

use crate::{
    ast::{self, Decl, Expr, Import, Module},
    driver::RayPaths,
    errors::{RayError, RayErrorKind, RayResult},
    libgen::RayLib,
    lir::Program,
    parse::{self, ParseOptions, Parser},
    pathlib::FilePath,
    span::{Source, SourceMap, Span},
    strutils, transform,
    typing::{
        state::{Env, SchemeEnv},
        ty::{Ty, TyVar},
        TyCtx,
    },
};

use std::{
    collections::{HashMap, HashSet},
    fs,
};

const C_STANDARD_INCLUDE_PATHS: [&'static str; 2] = ["/usr/include", "/usr/local/include"];

#[derive(Debug)]
pub struct ModuleBuilder<'a, A, B>
where
    A: std::fmt::Debug + Clone + PartialEq + Eq,
    B: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub modules: HashMap<ast::Path, Module<A, B>>,
    pub srcmaps: HashMap<ast::Path, SourceMap>,
    pub libs: HashMap<ast::Path, RayLib>,
    no_core: bool,
    input_paths: HashSet<ast::Path>,
    paths: &'a RayPaths,
    c_include_paths: Vec<FilePath>,
}

impl ModuleBuilder<'_, Expr, Decl> {
    pub fn new(
        paths: &RayPaths,
        c_include_paths: Vec<FilePath>,
        no_core: bool,
    ) -> ModuleBuilder<Expr, Decl> {
        ModuleBuilder {
            paths,
            c_include_paths,
            no_core,
            modules: HashMap::new(),
            srcmaps: HashMap::new(),
            libs: HashMap::new(),
            input_paths: HashSet::new(),
        }
    }

    fn build(
        &mut self,
        mut root_file: ast::File,
        mut srcmap: SourceMap,
        root_fp: &FilePath,
        input_path: &FilePath,
        module_path: ast::Path,
    ) -> Result<ast::Path, Vec<RayError>> {
        let mut errs = vec![];

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
                    Err(e) => errs.push(e),
                }
            }

            // collect submodules
            for (f, m) in submod_paths {
                match self.build_from_path(&f, Some(m)) {
                    Ok(m) => submodules.push(m),
                    Err(e) => errs.extend(e),
                }
            }
        }

        // collect from imports
        let mut imports = vec![];

        if !self.no_core {
            // first add the core if it hasn't been added already
            let core_path = ast::Path::from(vec![str!("core")]);
            if !self.input_paths.contains(&core_path) {
                let core_fp = &self.paths.get_stdlib_path() / "core";
                match self.build_from_path(&core_fp, Some(core_path)) {
                    Ok(m) => imports.push(m),
                    Err(e) => errs.extend(e),
                }
            }
        }

        // then build all of the imports from the root file
        let mut c_decl_set = HashSet::new();
        for import in root_file.imports.iter() {
            match self.resolve_import(&root_file.filepath, import) {
                Ok(fpath) => {
                    if import.c_import.is_some() {
                        if let Ok(tys) = parse::cparse(&fpath, &self.c_include_paths) {
                            for (ty, span) in tys {
                                let decl = ty.convert_to_decl(span);
                                let key = decl.to_string();
                                if !c_decl_set.contains(&key) {
                                    decls.push(decl);
                                    c_decl_set.insert(key);
                                }
                            }
                        }
                    } else {
                        match self.build_from_path(&fpath, Some(import.path.value.clone())) {
                            Ok(m) => imports.push(m),
                            Err(e) => errs.extend(e),
                        }
                    }
                }
                Err(e) => errs.push(e),
            }
        }

        if errs.len() != 0 {
            Err(errs)
        } else {
            self.srcmaps.insert(module_path.clone(), srcmap);
            self.modules.insert(
                module_path.clone(),
                Module {
                    submodules,
                    imports,
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
            Ok(module_path)
        }
    }

    #[allow(dead_code)]
    pub fn build_from_src(
        &mut self,
        src: String,
        module_path: ast::Path,
    ) -> Result<ast::Path, Vec<RayError>> {
        // check if module has already been built
        if self.input_paths.contains(&module_path) {
            return Ok(module_path);
        }

        self.input_paths.insert(module_path.clone());

        let mut srcmap = SourceMap::new();
        let root_file = Parser::parse_from_src(
            src,
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
    ) -> Result<ast::Path, Vec<RayError>> {
        let root_fp = self.get_root_module(input_path, &module_path)?;
        let module_path = module_path.unwrap_or_else(|| ast::Path::from(input_path.clone()));

        // check if module has already been built
        if self.input_paths.contains(&module_path) {
            return Ok(module_path);
        }

        self.input_paths.insert(module_path.clone());

        // the library file can be used instead
        if root_fp.has_extension("raylib") || root_fp.file_name() == ".raylib" {
            self.load_library(root_fp, &module_path)?;
            return Ok(module_path);
        }

        let mut srcmap = SourceMap::new();
        let root_file = self.build_file(&mut srcmap, &root_fp, &module_path)?;
        self.build(root_file, srcmap, &root_fp, input_path, module_path)
    }

    fn build_file(
        &mut self,
        srcmap: &mut SourceMap,
        input_path: &FilePath,
        module_path: &ast::Path,
    ) -> Result<ast::File, RayError> {
        log::info!("parsing {}", input_path);
        let filepath = input_path.clone();
        let original_filepath = input_path.clone();
        Parser::parse(
            ParseOptions {
                filepath,
                original_filepath,
                module_path: module_path.clone(),
                use_stdin: false,
            },
            srcmap,
        )
    }

    pub fn get_root_module(
        &self,
        path: &FilePath,
        module_path: &Option<ast::Path>,
    ) -> Result<FilePath, RayError> {
        // first if not an entrypoint, check if there's a
        // pre-built .raylib in the build cache on disk
        let is_entrypoint = module_path.is_none();
        if let Some(module_path) = module_path {
            let build_path = self.paths.get_build_path();
            log::debug!("build_path: {}", build_path);
            let lib_path = (build_path / module_path.join("#")).with_extension("raylib");
            log::debug!("lib_path: {}", lib_path);
            if lib_path.exists() {
                return Ok(lib_path);
            }
        }

        if path.exists() && !path.is_dir() {
            Ok(path.clone())
        } else if path.is_dir() {
            // we found a directory matching the name of the module
            // let's look for a .raylib, mod.ray, module.ray, or BASE.ray file
            // note: .raylib must be first
            let base = path.file_name();
            for name in [".raylib", "module.ray", "mod.ray", &format!("{}.ray", base)].iter() {
                if *name == ".raylib" && is_entrypoint {
                    // we want to ignore .raylib in the case that we're building
                    // the module that is contained in the .raylib itself
                    continue;
                }

                let fp = path / name;
                if fp.exists() {
                    return Ok(fp);
                }
            }

            Err(RayError {
                msg: format!(
                    "No root module file. mod.ray, module.ray, or {base}.ray should exist in the directory {path}",
                    base=base, path=path
                ),
                src: vec![Source {
                    filepath: path.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
            })
        } else {
            Err(RayError {
                msg: format!("{} does not exist or is not a directory", path),
                src: vec![Source {
                    filepath: path.clone(),
                    ..Default::default()
                }],
                kind: RayErrorKind::IO,
            })
        }
    }

    fn load_library(&mut self, lib_path: FilePath, module_path: &ast::Path) -> RayResult<()> {
        let lib = match bincode::deserialize_from(fs::File::open(&lib_path)?) {
            Ok(l) => l,
            Err(e) => {
                return Err(RayError {
                    msg: format!("Failed loading library file {}: {}", lib_path, e),
                    src: vec![Source {
                        filepath: lib_path,
                        ..Default::default()
                    }],
                    kind: RayErrorKind::Parse,
                })
            }
        };
        self.libs.insert(module_path.clone(), lib);
        Ok(())
    }

    fn resolve_import(
        &mut self,
        parent_filepath: &FilePath,
        import: &Import,
    ) -> Result<FilePath, RayError> {
        if let Some((ref include, sp)) = import.c_import {
            return self.resolve_c_include(&include, parent_filepath, sp);
        }

        let module_path = &import.path.value;
        let curr_dirpath = if parent_filepath.is_dir() {
            parent_filepath.clone()
        } else {
            parent_filepath.dir()
        };

        let stdlib_path = self.paths.get_stdlib_path();
        let paths_to_check = vec![&stdlib_path, &curr_dirpath];
        let module_fp = &module_path.to_filepath();
        let span = Some(import.span);
        let mut possible_paths = vec![];
        for p in paths_to_check {
            let fname = format!("{}.ray", module_fp.file_name());
            let fpath = p / fname;
            if fpath.exists() {
                possible_paths.push(fpath);
                continue;
            }

            // check if module directory exists
            let dirpath = p / module_fp;
            if dirpath.as_ref().is_dir() {
                // we found a directory matching the name of the module
                // let's look for a module.ray or BASE.ray file
                let mut fpath = &dirpath / "module.ray";
                possible_paths.push(if fpath.exists() {
                    fpath
                } else {
                    let base = &format!("{}.ray", module_path.name().unwrap());
                    fpath = &dirpath / base;
                    if fpath.exists() {
                        fpath
                    } else {
                        // no "root" module file
                        let dirbase = dirpath.file_name();
                        return Err(RayError {
                            msg: format!(
                                "Root module file does not exist. Either {dirbase}/module.ray or {dirbase}/{base} is required.",
                                dirbase=dirbase,
                                base=base,
                            ),
                            src: vec![Source {
                                filepath: parent_filepath.clone(),
                                span,
                                ..Default::default()
                            }],
                            kind: RayErrorKind::Import,
                        })
                    }
                });
            }
        }

        if possible_paths.len() == 0 {
            Err(RayError {
                msg: format!("Could not find module from import {}", module_path),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span,
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
            })
        } else if possible_paths.len() > 1 {
            Err(RayError {
                msg: format!(
                    "Ambiguous import {}. Found multiple file paths:\n{}",
                    module_path,
                    strutils::indent_lines_iter(&possible_paths, 2),
                ),
                src: vec![Source {
                    filepath: parent_filepath.clone(),
                    span,
                    ..Default::default()
                }],
                kind: RayErrorKind::Import,
            })
        } else {
            Ok(possible_paths.pop().unwrap())
        }
    }

    fn resolve_c_include(
        &mut self,
        include: &str,
        src_path: &FilePath,
        span: Span,
    ) -> Result<FilePath, RayError> {
        let mut include_paths = vec![];

        // add the includes from the build options
        include_paths.extend(self.c_include_paths.clone());

        // add the standard include paths
        include_paths.extend(C_STANDARD_INCLUDE_PATHS.iter().map(FilePath::from));

        for p in include_paths {
            let fp = p / include;
            if fp.exists() {
                return Ok(fp);
            }
        }

        Err(RayError {
            kind: RayErrorKind::Import,
            msg: format!("Could not find C header file {:?}", include),
            src: vec![Source {
                filepath: src_path.clone(),
                span: Some(span),
                ..Default::default()
            }],
        })
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

    pub fn finish(
        self,
        module_path: &ast::Path,
    ) -> RayResult<(Module<(), Decl>, TyCtx, SourceMap, SchemeEnv, Vec<Program>)> {
        let mut libs = vec![];
        let mut modules = self.modules;
        let mut srcmaps = self.srcmaps;
        let mut lib_set = HashSet::new();
        let mut lib_defs = Env::new();
        let mut tcx = TyCtx::new();
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
            srcmaps.insert(lib_path, lib.srcmap);
            libs.push(lib.program);
            lib_defs.extend(lib.defs);
        }

        let (module, srcmap, _) =
            transform::combine(module_path, &mut modules, &mut srcmaps, &lib_set, &mut tcx)?;
        Ok((module, tcx, srcmap, lib_defs, libs))
    }
}
