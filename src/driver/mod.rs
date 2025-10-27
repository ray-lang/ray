use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    env, fs,
    path::PathBuf,
};

use itertools::Itertools;
use top::{Subst, Substitutable};

use crate::{
    ast::{Assign, CurlyElement, Decl, Expr, FnParam, Func, Module, Node, Path, Pattern},
    codegen::llvm,
    errors::{RayError, RayErrorKind},
    libgen, lir,
    pathlib::FilePath,
    sema::{self, SymbolBuildContext, SymbolMap, build_symbol_map},
    span::{SourceMap, Span},
    typing::{
        InferSystem, TyCtx,
        state::SchemeEnv,
        ty::{Ty, TyScheme, TyVar},
    },
};

mod analyze;
mod build;

pub use analyze::{
    AnalysisFormat, AnalysisReport, AnalyzeOptions, DefinitionInfo, SymbolInfo, SymbolKind,
    TypeInfo,
};
pub use build::BuildOptions;

pub struct FrontendResult {
    pub module_path: Path,
    pub module: Module<(), Decl>,
    pub tcx: TyCtx,
    pub ncx: sema::NameContext,
    pub srcmap: SourceMap,
    pub symbol_map: SymbolMap,
    pub defs: SchemeEnv,
    pub libs: Vec<lir::Program>,
    pub paths: HashSet<Path>,
    pub definitions: HashMap<Path, libgen::DefinitionRecord>,
}

#[derive(Debug, Clone, Default)]
pub struct RayPaths {
    root: FilePath,
}

impl RayPaths {
    pub fn new(root: FilePath) -> Self {
        Self { root }
    }

    pub fn discover(explicit: Option<FilePath>, workspace_hint: Option<&FilePath>) -> Option<Self> {
        fn has_toolchain_root(candidate: &FilePath) -> bool {
            (candidate / "lib" / "core").exists()
        }

        let mut candidates: Vec<FilePath> = Vec::new();

        if let Some(path) = explicit {
            candidates.push(path);
        }

        if let Ok(path) = env::var("RAY_PATH") {
            if !path.is_empty() {
                candidates.push(FilePath::from(PathBuf::from(path)));
            }
        }

        if let Some(hint) = workspace_hint {
            candidates.push(hint.clone());
        }

        if let Some(home) = home::home_dir() {
            candidates.push(FilePath::from(home) / ".ray");
        }

        candidates.push(FilePath::from("/opt/ray"));

        candidates
            .into_iter()
            .find(|candidate| has_toolchain_root(candidate))
            .map(Self::new)
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_empty()
    }

    pub fn get_build_path(&self) -> FilePath {
        &self.root / "build"
    }

    pub fn get_lib_path(&self) -> FilePath {
        &self.root / "lib"
    }

    pub fn get_c_includes_path(&self) -> FilePath {
        &self.root / "wasi-sysroot" / "include"
    }
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
            max_optimize_level: 2,
            emit_ir: false,
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
                let symbols = collect_symbols(&frontend);
                let definitions = collect_definitions(&frontend);
                let types = collect_types(&frontend);
                AnalysisReport::new(format, input_path, Vec::new(), symbols, types, definitions)
            }
            Err(errs) => {
                AnalysisReport::new(format, input_path, errs, Vec::new(), Vec::new(), Vec::new())
            }
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
            sema::ModuleBuilder::new(&self.ray_paths, c_include_paths, options.no_core);
        let module_scope =
            match mod_builder.build_from_path_with_overlay(&options.input_path, None, overlays)? {
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

        let mut inf = InferSystem::new(&mut result.tcx, &mut result.ncx);
        let (solution, defs) = match inf.infer_ty(&result.module, &result.srcmap, &result.defs) {
            Ok(result) => result,
            Err(errs) => {
                return Err(errs
                    .into_iter()
                    .map(|err| RayError {
                        msg: err.message(),
                        src: err.src,
                        kind: RayErrorKind::Type,
                        context: Some(format!("while type checking {module_path}")),
                    })
                    .collect());
            }
        };

        log::debug!("solution: {}", solution);

        result.apply_solution(solution, &defs);

        let definitions =
            libgen::collect_definition_records(&result.module, &result.srcmap, &result.tcx);

        let symbol_map = build_symbol_map(SymbolBuildContext::new(&result.module, &result.srcmap));

        Ok(FrontendResult {
            module_path,
            module: result.module,
            tcx: result.tcx,
            ncx: result.ncx,
            srcmap: result.srcmap,
            symbol_map,
            defs,
            libs: result.libs,
            paths: result.paths,
            definitions,
        })
    }

    pub fn emit_errors(&mut self, errs: Vec<RayError>) {
        for ((kind, src), group) in &errs.into_iter().group_by(|err| (err.kind, err.src.clone())) {
            let group_errs = group.collect::<Vec<_>>();
            let msg = group_errs
                .iter()
                .map(|err| err.msg.clone())
                .collect::<Vec<_>>()
                .join("\n");
            let context = group_errs
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
        let paths = self.ray_paths.clone();

        let frontend = self.build_frontend(&options, None)?;

        if options.no_compile {
            return Ok(());
        }

        let FrontendResult {
            module_path,
            module,
            tcx,
            ncx,
            srcmap,
            symbol_map: _,
            defs,
            libs,
            paths: module_paths,
            definitions: _,
        } = frontend;

        let mut program = lir::Program::generate(&module, &tcx, &srcmap, libs)?;
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
            let lib = libgen::serialize(program, tcx, ncx, srcmap, defs, modules, definitions);
            let path = output_path("raylib");
            let build_path = paths.get_build_path();
            if !build_path.exists() {
                fs::create_dir_all(build_path).map_err(|err| vec![err.into()])?;
            }

            let cache_path =
                (paths.get_build_path() / module_path.join("#")).with_extension("raylib");
            log::info!("writing to {}", path);
            fs::write(cache_path, &lib)
                .and_then(|_| fs::write(path, lib))
                .map_err(|err| vec![err.into()])
        } else {
            log::debug!("program before monomorphization:\n{}", program);
            program.monomorphize();
            log::debug!("program after monomorphization:\n{}", program);

            let lcx = inkwell::context::Context::create();
            let target = options.get_target();
            llvm::codegen(&program, &tcx, &srcmap, &lcx, &target, output_path)
        }
    }
}

fn collect_symbols(frontend: &FrontendResult) -> Vec<SymbolInfo> {
    let mut symbols = Vec::new();
    let mut seen = HashSet::new();

    for decl in &frontend.module.decls {
        let source = frontend.srcmap.get(decl);
        let span = source.span;
        let filepath = source.filepath.clone();
        let doc = frontend.srcmap.doc(decl).cloned();

        match &decl.value {
            Decl::Func(func) => {
                let name = func.sig.path.to_string();
                if !seen.insert(name.clone()) {
                    continue;
                }
                let ty = type_info_for_node(&frontend.tcx, decl.id).map(|(ty, _)| ty);
                symbols.push(SymbolInfo {
                    id: decl.id,
                    name,
                    kind: SymbolKind::Function,
                    filepath: filepath.clone(),
                    span,
                    ty,
                    parent_id: None, // Functions currently have no parent
                    doc: doc.clone(),
                });
            }
            Decl::Struct(st) => {
                let name = st.path.value.to_string();
                if !seen.insert(name.clone()) {
                    continue;
                }
                let struct_id = decl.id;
                symbols.push(SymbolInfo {
                    id: struct_id,
                    name,
                    kind: SymbolKind::Struct,
                    filepath: filepath.clone(),
                    span,
                    ty: None,
                    parent_id: None, // Top-level struct
                    doc: doc.clone(),
                });

                if let Some(fields) = &st.fields {
                    for field in fields {
                        let field_name = field.to_string();
                        let field_source = frontend.srcmap.get(field);
                        let field_span = field_source.span;
                        let field_doc = frontend.srcmap.doc(field).cloned();
                        symbols.push(SymbolInfo {
                            id: field.id,
                            name: field_name,
                            kind: SymbolKind::Field,
                            filepath: field_source.filepath.clone(),
                            span: field_span,
                            ty: type_info_for_node(&frontend.tcx, field.id).map(|(ty, _)| ty),
                            parent_id: Some(struct_id), // Field belongs to this struct
                            doc: field_doc,
                        });
                    }
                }
            }
            Decl::Trait(tr) => {
                let name = tr.ty.to_string();
                if !seen.insert(name.clone()) {
                    continue;
                }
                symbols.push(SymbolInfo {
                    id: decl.id,
                    name,
                    kind: SymbolKind::Trait,
                    filepath: filepath.clone(),
                    span,
                    ty: None,
                    parent_id: None, // Top-level trait
                    doc: doc.clone(),
                });
            }
            Decl::TypeAlias(alias_name, alias_ty) => {
                let name = alias_name.value.path.to_string();
                if !seen.insert(name.clone()) {
                    continue;
                }
                symbols.push(SymbolInfo {
                    id: decl.id,
                    name,
                    kind: SymbolKind::TypeAlias,
                    filepath: filepath.clone(),
                    span,
                    ty: Some(alias_ty.to_string()),
                    parent_id: None, // Top-level type alias
                    doc: doc.clone(),
                });
            }
            _ => {}
        }
    }
    symbols
}

fn type_info_for_node(tcx: &TyCtx, node_id: u64) -> Option<(String, bool)> {
    if let Some(scheme) = tcx.maybe_ty_scheme_of(node_id) {
        Some((pretty_print_scheme(&scheme), true))
    } else if let Some(ty) = tcx.get_ty(node_id) {
        Some((pretty_print_ty(&ty), false))
    } else {
        None
    }
}

fn collect_types(frontend: &FrontendResult) -> Vec<TypeInfo> {
    let mut types = Vec::new();

    for decl in &frontend.module.decls {
        maybe_push_node_type(&mut types, &frontend.tcx, &frontend.srcmap, decl);

        if let Decl::Func(func) = &decl.value {
            for param in &func.sig.params {
                maybe_push_node_type(&mut types, &frontend.tcx, &frontend.srcmap, param);
            }

            if let Some(body) = &func.body {
                maybe_push_node_type(&mut types, &frontend.tcx, &frontend.srcmap, body);
            }
        }
    }

    types.sort_by(|a, b| {
        a.filepath
            .cmp(&b.filepath)
            .then_with(|| compare_span(a.span, b.span))
            .then_with(|| a.id.cmp(&b.id))
    });

    log::debug!("collected {} type entries", types.len());

    types
}

fn collect_definitions(frontend: &FrontendResult) -> Vec<DefinitionInfo> {
    let mut definitions = Vec::new();
    let mut seen_usage_ids = HashSet::new();

    // Prefer specialized call resolutions (e.g., trait method dispatch) before generic name matches.
    for (usage_id, path) in frontend.tcx.call_resolutions() {
        push_definition_entry(
            frontend,
            &mut definitions,
            &mut seen_usage_ids,
            *usage_id,
            path,
        );
    }

    let mut name_refs = Vec::new();
    for decl in &frontend.module.decls {
        collect_decl_name_refs(decl, &mut name_refs);
    }

    for (usage_id, path) in name_refs {
        push_definition_entry(
            frontend,
            &mut definitions,
            &mut seen_usage_ids,
            usage_id,
            &path,
        );
    }

    definitions.sort_by(|a, b| {
        a.usage_filepath
            .cmp(&b.usage_filepath)
            .then_with(|| compare_span(a.usage_span, b.usage_span))
            .then_with(|| a.usage_id.cmp(&b.usage_id))
    });

    log::debug!("collected {} definition entries", definitions.len());

    definitions
}

fn push_definition_entry(
    frontend: &FrontendResult,
    out: &mut Vec<DefinitionInfo>,
    seen: &mut HashSet<u64>,
    usage_id: u64,
    path: &Path,
) {
    if !seen.insert(usage_id) {
        return;
    }

    let usage_source = match frontend.srcmap.get_by_id(usage_id) {
        Some(src) => src,
        None => return,
    };

    let usage_path = libgen::display_path(path);
    let usage_key = libgen::canonical_path_key(path);
    let usage_filepath = usage_source.filepath.clone();
    let usage_span = usage_source.span;

    let (definition_id, definition_path, definition_filepath, definition_span, definition_doc) =
        if let Some(entry) = frontend.definitions.get(&usage_key) {
            let mut def_filepath = entry.file.clone();
            let mut def_span = entry.span;
            let mut def_doc = entry.doc.clone();

            if def_filepath.is_none() || def_span.is_none() {
                if let Some(src) = frontend.srcmap.get_by_id(entry.id) {
                    if def_filepath.is_none() {
                        def_filepath = Some(src.filepath.clone());
                    }
                    if def_span.is_none() {
                        def_span = src.span;
                    }
                    if def_doc.is_none() {
                        def_doc = frontend.srcmap.doc_by_id(entry.id).cloned();
                    }
                }
            }

            (
                Some(entry.id),
                Some(entry.display_path.clone()),
                def_filepath,
                def_span,
                def_doc,
            )
        } else {
            (None, None, None, None, None)
        };

    out.push(DefinitionInfo {
        usage_id,
        usage_path,
        usage_filepath,
        usage_span,
        definition_id,
        definition_path,
        definition_filepath,
        definition_span,
        definition_doc,
    });
}

fn collect_decl_name_refs(decl: &Node<Decl>, refs: &mut Vec<(u64, Path)>) {
    match &decl.value {
        Decl::Func(func) => collect_func_refs(func, refs),
        Decl::Extern(ext) => collect_decl_name_refs(ext.decl_node(), refs),
        Decl::Declare(assign) => {
            collect_assign_refs(assign, refs);
        }
        Decl::Trait(tr) => {
            for field in &tr.fields {
                collect_decl_name_refs(field, refs);
            }
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func in funcs {
                    collect_func_refs(&func.value, refs);
                }
            }
            if let Some(externs) = &im.externs {
                for ext in externs {
                    collect_decl_name_refs(ext, refs);
                }
            }
            if let Some(consts) = &im.consts {
                for assign in consts {
                    collect_assign_refs(&assign.value, refs);
                }
            }
        }
        Decl::FnSig(_) | Decl::Struct(_) | Decl::TypeAlias(_, _) => {}
        Decl::Mutable(_) | Decl::Name(_) => {}
    }
}

fn collect_assign_refs(assign: &Assign, refs: &mut Vec<(u64, Path)>) {
    collect_pattern_refs(&assign.lhs.value, refs);
    collect_expr_name_refs(&assign.rhs, refs);
}

fn collect_func_refs(func: &Func, refs: &mut Vec<(u64, Path)>) {
    for param in &func.sig.params {
        collect_fn_param_refs(&param.value, refs);
    }
    if let Some(body) = &func.body {
        collect_expr_name_refs(body, refs);
    }
}

fn collect_fn_param_refs(param: &FnParam, refs: &mut Vec<(u64, Path)>) {
    match param {
        FnParam::Name(_) | FnParam::Missing { .. } => {}
        FnParam::DefaultValue(default_param, value) => {
            collect_fn_param_refs(&default_param.value, refs);
            collect_expr_name_refs(value, refs);
        }
    }
}

fn collect_pattern_refs(pattern: &Pattern, refs: &mut Vec<(u64, Path)>) {
    match pattern {
        Pattern::Missing(_) | Pattern::Name(_) | Pattern::Deref(_) => {}
        Pattern::Sequence(patterns) | Pattern::Tuple(patterns) => {
            for pat in patterns {
                collect_pattern_refs(&pat.value, refs);
            }
        }
    }
}

fn collect_expr_name_refs(expr: &Node<Expr>, refs: &mut Vec<(u64, Path)>) {
    match &expr.value {
        Expr::Name(name) => refs.push((expr.id, name.path.clone())),
        Expr::Path(path) => refs.push((expr.id, path.clone())),
        Expr::Assign(assign) => {
            collect_pattern_refs(&assign.lhs.value, refs);
            collect_expr_name_refs(&assign.rhs, refs);
        }
        Expr::Asm(_) => {}
        Expr::BinOp(bin) => {
            collect_expr_name_refs(&bin.lhs, refs);
            collect_expr_name_refs(&bin.rhs, refs);
        }
        Expr::Block(block) => {
            for stmt in &block.stmts {
                collect_expr_name_refs(stmt, refs);
            }
        }
        Expr::Break(value) => {
            if let Some(v) = value {
                collect_expr_name_refs(v, refs);
            }
        }
        Expr::Call(call) => {
            collect_expr_name_refs(&call.callee, refs);
            for arg in &call.args.items {
                collect_expr_name_refs(arg, refs);
            }
        }
        Expr::Cast(cast) => collect_expr_name_refs(&cast.lhs, refs),
        Expr::Closure(closure) => {
            for arg in &closure.args.items {
                collect_expr_name_refs(arg, refs);
            }
            collect_expr_name_refs(&closure.body, refs);
        }
        Expr::Curly(curly) => {
            for element in &curly.elements {
                collect_curly_element_refs(element, refs);
            }
        }
        Expr::DefaultValue(value) => collect_expr_name_refs(value, refs),
        Expr::Dot(dot) => {
            collect_expr_name_refs(&dot.lhs, refs);
            refs.push((dot.rhs.id, dot.rhs.value.path.clone()));
        }
        Expr::Func(func) => collect_func_refs(func, refs),
        Expr::For(for_expr) => {
            collect_pattern_refs(&for_expr.pat.value, refs);
            collect_expr_name_refs(&for_expr.expr, refs);
            collect_expr_name_refs(&for_expr.body, refs);
        }
        Expr::If(ifexpr) => {
            collect_expr_name_refs(&ifexpr.cond, refs);
            collect_expr_name_refs(&ifexpr.then, refs);
            if let Some(else_) = &ifexpr.els {
                collect_expr_name_refs(else_, refs);
            }
        }
        Expr::Index(index) => {
            collect_expr_name_refs(&index.lhs, refs);
            collect_expr_name_refs(&index.index, refs);
        }
        Expr::Labeled(label, value) => {
            collect_expr_name_refs(label, refs);
            collect_expr_name_refs(value, refs);
        }
        Expr::List(list) => {
            for item in &list.items {
                collect_expr_name_refs(item, refs);
            }
        }
        Expr::Literal(_) => {}
        Expr::Loop(loop_expr) => collect_expr_name_refs(&loop_expr.body, refs),
        Expr::New(new_expr) => {
            if let Some(count) = &new_expr.count {
                collect_expr_name_refs(count, refs);
            }
        }
        Expr::Pattern(_) => {}
        Expr::Paren(value) => collect_expr_name_refs(value, refs),
        Expr::Range(range) => {
            collect_expr_name_refs(&range.start, refs);
            collect_expr_name_refs(&range.end, refs);
        }
        Expr::Return(value) => {
            if let Some(v) = value {
                collect_expr_name_refs(v, refs);
            }
        }
        Expr::Sequence(seq) => {
            for item in &seq.items {
                collect_expr_name_refs(item, refs);
            }
        }
        Expr::Tuple(tuple) => {
            for item in &tuple.seq.items {
                collect_expr_name_refs(item, refs);
            }
        }
        Expr::Type(_) => {}
        Expr::TypeAnnotated(value, _) => collect_expr_name_refs(value, refs),
        Expr::UnaryOp(unary) => collect_expr_name_refs(&unary.expr, refs),
        Expr::Unsafe(value) => collect_expr_name_refs(value, refs),
        Expr::While(while_expr) => {
            collect_expr_name_refs(&while_expr.cond, refs);
            collect_expr_name_refs(&while_expr.body, refs);
        }
        Expr::Missing(_) => {}
    }
}

fn collect_curly_element_refs(element: &Node<CurlyElement>, refs: &mut Vec<(u64, Path)>) {
    match &element.value {
        CurlyElement::Name(name) => refs.push((element.id, name.path.clone())),
        CurlyElement::Labeled(name, expr) => {
            refs.push((element.id, name.path.clone()));
            collect_expr_name_refs(expr, refs);
        }
    }
}

fn compare_span(a: Option<Span>, b: Option<Span>) -> Ordering {
    match (a, b) {
        (Some(a), Some(b)) => (a.start.lineno, a.start.col, a.end.lineno, a.end.col).cmp(&(
            b.start.lineno,
            b.start.col,
            b.end.lineno,
            b.end.col,
        )),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

fn maybe_push_node_type<T>(
    entries: &mut Vec<TypeInfo>,
    tcx: &TyCtx,
    srcmap: &SourceMap,
    node: &Node<T>,
) {
    if let Some((ty_str, is_scheme)) = type_info_for_node(tcx, node.id) {
        let source = srcmap.get(node);
        entries.push(TypeInfo {
            id: node.id,
            filepath: source.filepath.clone(),
            span: source.span,
            ty: ty_str,
            is_scheme,
        });
    }
}

fn pretty_print_scheme(scheme: &TyScheme) -> String {
    let mut scheme = scheme.clone();
    normalize_scheme_tyvars(&mut scheme);
    scheme.to_string()
}

fn pretty_print_ty(ty: &Ty) -> String {
    let mut ty = ty.clone();
    normalize_tyvars(&mut ty);
    ty.to_string()
}

fn normalize_scheme_tyvars(scheme: &mut TyScheme) {
    let mut subst = Subst::<TyVar, Ty>::new();
    let mut counter = 0usize;

    {
        let quantifiers = scheme.quantifiers().clone();
        collect_unknown_vars(&quantifiers, &mut subst, &mut counter);
    }

    let mono_free_vars = scheme.mono().free_vars();
    collect_unknown_vars(mono_free_vars, &mut subst, &mut counter);
    let qualifier_free_vars = scheme.qualifiers().free_vars();
    collect_unknown_vars(qualifier_free_vars, &mut subst, &mut counter);

    if !subst.is_empty() {
        scheme.apply_subst_all(&subst);
    }
}

fn normalize_tyvars(ty: &mut Ty) {
    let mut subst = Subst::<TyVar, Ty>::new();
    let mut counter = 0usize;
    let free_vars = ty.free_vars();
    collect_unknown_vars(free_vars, &mut subst, &mut counter);
    if !subst.is_empty() {
        ty.apply_subst_all(&subst);
    }
}

fn collect_unknown_vars<'a, I>(vars: I, subst: &mut Subst<TyVar, Ty>, counter: &mut usize)
where
    I: IntoIterator<Item = &'a TyVar>,
{
    for var in vars {
        assign_pretty_name_for_var(var, subst, counter);
    }
}

fn assign_pretty_name_for_var(var: &TyVar, subst: &mut Subst<TyVar, Ty>, counter: &mut usize) {
    if !var.is_unknown() {
        return;
    }

    if subst.contains_key(var) {
        return;
    }

    let new_var = fresh_pretty_tyvar(*counter);
    *counter += 1;
    subst.insert(var.clone(), Ty::Var(new_var));
}

fn fresh_pretty_tyvar(index: usize) -> TyVar {
    TyVar::from(pretty_tyvar_name(index))
}

fn pretty_tyvar_name(index: usize) -> String {
    let letter = (b'a' + (index % 26) as u8) as char;
    let suffix = index / 26;
    if suffix == 0 {
        format!("'{}", letter)
    } else {
        format!("'{}{}", letter, suffix)
    }
}
