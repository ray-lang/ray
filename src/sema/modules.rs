use crate::ast::{self, Import, Module};
use crate::errors::{RayError, RayErrorKind};
use crate::parse::{self, ParseOptions, Parser};
use crate::pathlib::FilePath;
use crate::span::Span;
use crate::strutils;

use std::collections::{HashMap, HashSet};

const C_STANDARD_INCLUDE_PATHS: [&'static str; 2] = ["/usr/include", "/usr/local/include"];

#[derive(Debug)]
pub struct ModuleBuilder {
    pub modules: HashMap<ast::Path, Module>,
    paths: HashSet<ast::Path>,
    libpath: FilePath,
    c_include_paths: Vec<FilePath>,
}

impl ModuleBuilder {
    pub fn new(libpath: FilePath, c_include_paths: Vec<FilePath>) -> ModuleBuilder {
        ModuleBuilder {
            libpath,
            c_include_paths,
            modules: HashMap::new(),
            paths: HashSet::new(),
        }
    }

    fn build(
        &mut self,
        mut root_file: ast::File,
        root_fp: &FilePath,
        input_path: &FilePath,
        module_path: ast::Path,
        mut next_ast_id: u64,
    ) -> Result<ast::Path, Vec<RayError>> {
        let module_id = module_path.to_id();
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
                match self.build_file(&fp, &module_path, next_ast_id) {
                    Ok(f) => {
                        next_ast_id = f.last_ast_id;
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

        // first add the core if it hasn't been added already
        let core_path = ast::Path::from(vec![str!("core")]);
        if !self.paths.contains(&core_path) {
            let src = include_str!("../../intrinsics/core.ray");
            match self.build_from_src(src.to_string(), core_path) {
                Ok(m) => imports.push(m),
                Err(e) => errs.extend(e),
            }
        }

        let mut c_decl_set = HashSet::new();
        for import in root_file.imports.iter() {
            match self.resolve_import(&root_file.filepath, import) {
                Ok(fpath) => {
                    if import.c_import.is_some() {
                        if let Ok(tys) = parse::cparse(&fpath, &self.c_include_paths) {
                            for (ty, span) in tys {
                                let decl = ty.convert_to_decl(span, module_id, &mut next_ast_id);
                                let key = decl.to_string();
                                if !c_decl_set.contains(&key) {
                                    decls.push(decl);
                                    c_decl_set.insert(key);
                                }
                            }
                        }
                    } else {
                        match self.build_from_path(&fpath, Some(import.path.clone())) {
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
            self.modules.insert(
                module_path.clone(),
                Module {
                    submodules,
                    imports,
                    stmts,
                    decls,
                    filepaths,
                    path: module_path.clone(),
                    doc_comment: root_file.doc_comment,
                },
            );
            Ok(module_path)
        }
    }

    pub fn build_from_src(
        &mut self,
        src: String,
        module_path: ast::Path,
    ) -> Result<ast::Path, Vec<RayError>> {
        let mut next_ast_id = 1_u64;

        // check if module has already been built
        if self.paths.contains(&module_path) {
            return Ok(module_path);
        }

        self.paths.insert(module_path.clone());

        let root_file = Parser::parse_from_src(
            src,
            ParseOptions {
                filepath: FilePath::new(),
                original_filepath: FilePath::new(),
                module_path: module_path.clone(),
                use_stdin: false,
            },
            next_ast_id,
        )?;

        next_ast_id = root_file.last_ast_id;

        // the "filepath"
        let fpath = FilePath::new();
        self.build(root_file, &fpath, &fpath, module_path, next_ast_id)
    }

    pub fn build_from_path(
        &mut self,
        input_path: &FilePath,
        module_path: Option<ast::Path>,
    ) -> Result<ast::Path, Vec<RayError>> {
        let mut next_ast_id = 1_u64;
        let root_fp = self.get_root_module(input_path)?;

        let module_path = module_path.unwrap_or_else(|| ast::Path::from(input_path));

        // check if module has already been built
        if self.paths.contains(&module_path) {
            return Ok(module_path);
        }

        self.paths.insert(module_path.clone());

        let root_file = self.build_file(&root_fp, &module_path, next_ast_id)?;
        next_ast_id = root_file.last_ast_id;

        self.build(root_file, &root_fp, input_path, module_path, next_ast_id)
    }

    fn build_file(
        &mut self,
        input_path: &FilePath,
        module_path: &ast::Path,
        next_ast_id: u64,
    ) -> Result<ast::File, RayError> {
        log::debug!("parsing {}", input_path);
        let filepath = input_path.clone();
        let original_filepath = input_path.clone();
        Parser::parse(
            ParseOptions {
                filepath,
                original_filepath,
                module_path: module_path.clone(),
                use_stdin: false,
            },
            next_ast_id,
        )
    }

    fn get_root_module(&mut self, path: &FilePath) -> Result<FilePath, RayError> {
        if path.exists() && !path.is_dir() {
            Ok(path.clone())
        } else if path.is_dir() {
            // we found a directory matching the name of the module
            // let's look for a module.ray or BASE.ray file
            let base = path.file_name();
            for name in ["module.ray", &format!("{}.ray", base)].iter() {
                let fp = path / name;
                if fp.exists() {
                    return Ok(fp);
                }
            }

            Err(RayError {
                msg: format!(
                    "No root module file. module.ray or {}.ray should exist in the directory {}",
                    base, path
                ),
                fp: path.clone(),
                span: None,
                kind: RayErrorKind::Import,
            })
        } else {
            Err(RayError {
                msg: format!("{} does not exist or is not a directory", path),
                fp: path.clone(),
                span: None,
                kind: RayErrorKind::IO,
            })
        }
    }

    fn resolve_import(
        &mut self,
        parent_filepath: &FilePath,
        import: &Import,
    ) -> Result<FilePath, RayError> {
        if let Some((ref include, sp)) = import.c_import {
            return self.resolve_c_include(&include, parent_filepath, sp);
        }

        let module_path = &import.path;
        let curr_dirpath = if parent_filepath.is_dir() {
            parent_filepath.clone()
        } else {
            parent_filepath.dir()
        };
        let paths_to_check = vec![&self.libpath, &curr_dirpath];
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
                            fp: parent_filepath.clone(),
                            kind: RayErrorKind::Import,
                            span,
                        })
                    }
                });
            }
        }

        if possible_paths.len() == 0 {
            Err(RayError {
                msg: format!("Could not find module from import {}", module_path),
                fp: parent_filepath.clone(),
                kind: RayErrorKind::Import,
                span,
            })
        } else if possible_paths.len() > 1 {
            Err(RayError {
                msg: format!(
                    "Ambiguous import {}. Found multiple file paths:\n{}",
                    module_path,
                    strutils::indent_lines_iter(&possible_paths, 2),
                ),
                fp: parent_filepath.clone(),
                kind: RayErrorKind::Import,
                span,
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
            fp: src_path.clone(),
            span: Some(span),
        })

        // for _, p := range includePaths {
        //     fullPath := filepath.Join(p, fpath)
        //     if _, err := os.Stat(fullPath); err == nil {
        //         return fullPath, nil
        //     }
        // }

        // return "", fmt.Errorf("Could not find C header file %q", fpath)
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
                } else {
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
}
