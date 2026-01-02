use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
    fs,
};

use ray_core::{
    ast::{Assign, CurlyElement, Decl, Expr, FnParam, Func, Module, Node, Pattern},
    codegen::{CodegenOptions, llvm},
    errors::{RayError, RayErrorKind},
    libgen, lir, passes,
    sema::{self, SymbolBuildContext, SymbolMap, build_symbol_map},
    sourcemap::SourceMap,
};
use ray_shared::{
    collections::namecontext::NameContext,
    node_id::NodeId,
    optlevel::OptLevel,
    pathlib::{FilePath, Path, RayPaths},
    span::{Source, Span},
};
use ray_typing::{TypecheckOptions, tyctx::TyCtx, types::Substitutable};

mod analyze;
mod build;
mod global_options;

pub use analyze::{
    AnalysisFormat, AnalysisReport, AnalyzeOptions, DefinitionInfo, SymbolInfo, SymbolKind,
    TypeInfo,
};
pub use build::BuildOptions;
pub use build::EmitType;
pub use global_options::*;

#[derive(Debug)]
pub struct FrontendResult {
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
                let symbols = collect_symbols(&frontend);
                let definitions = collect_definitions(&frontend);
                let types = collect_types(&frontend);
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
            sema::ModuleBuilder::new(&self.ray_paths, c_include_paths, options.no_core);
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
        let pass_manager =
            passes::FrontendPassManager::new(&result.module, &result.srcmap, &mut result.tcx);
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

        Ok(FrontendResult {
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
            module_path,
            module,
            tcx,
            ncx,
            srcmap,
            libs,
            paths: module_paths,
            bindings,
            closure_analysis,
            ..
        } = frontend;

        let mut program = lir::Program::generate(
            &module,
            &tcx,
            &ncx,
            &srcmap,
            &bindings,
            &closure_analysis,
            libs,
        )?;
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
                &tcx,
                &srcmap,
                &lcx,
                &target,
                output_path,
                codegen_options,
            )
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

fn type_info_for_node(tcx: &TyCtx, node_id: NodeId) -> Option<(String, bool)> {
    tcx.pretty_type_info_for_node(node_id)
}

fn collect_types(frontend: &FrontendResult) -> Vec<TypeInfo> {
    let mut types = Vec::new();

    for decl in &frontend.module.decls {
        // Top-level declarations: prefer schemes from defs, falling back to
        // TyCtx where needed.
        if let Some((ty_str, is_scheme)) = type_info_for_node(&frontend.tcx, decl.id) {
            let source = frontend.srcmap.get(decl);
            types.push(TypeInfo {
                id: decl.id,
                filepath: source.filepath.clone(),
                span: source.span,
                ty: ty_str,
                is_scheme,
            });
        }

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
    for (usage_id, resolution) in frontend.tcx.call_resolutions() {
        push_definition_entry(
            frontend,
            &mut definitions,
            &mut seen_usage_ids,
            *usage_id,
            &resolution.base_fqn,
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
    seen: &mut HashSet<NodeId>,
    usage_id: NodeId,
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
        if let Some(entry) = frontend.definitions_by_path.get(&usage_key) {
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

fn collect_decl_name_refs(decl: &Node<Decl>, refs: &mut Vec<(NodeId, Path)>) {
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

fn collect_assign_refs(assign: &Assign, refs: &mut Vec<(NodeId, Path)>) {
    collect_pattern_refs(&assign.lhs.value, refs);
    collect_expr_name_refs(&assign.rhs, refs);
}

fn collect_func_refs(func: &Func, refs: &mut Vec<(NodeId, Path)>) {
    for param in &func.sig.params {
        collect_fn_param_refs(&param.value, refs);
    }
    if let Some(body) = &func.body {
        collect_expr_name_refs(body, refs);
    }
}

fn collect_fn_param_refs(param: &FnParam, refs: &mut Vec<(NodeId, Path)>) {
    match param {
        FnParam::Name(_) | FnParam::Missing { .. } => {}
        FnParam::DefaultValue(default_param, value) => {
            collect_fn_param_refs(&default_param.value, refs);
            collect_expr_name_refs(value, refs);
        }
    }
}

fn collect_pattern_refs(pattern: &Pattern, refs: &mut Vec<(NodeId, Path)>) {
    match pattern {
        Pattern::Missing(_) | Pattern::Name(_) | Pattern::Deref(_) | Pattern::Dot(_, _) => {}
        Pattern::Index(lhs, index, _) => {
            collect_pattern_refs(&lhs.value, refs);
            collect_expr_name_refs(index.as_ref(), refs);
        }
        Pattern::Sequence(patterns) | Pattern::Tuple(patterns) => {
            for pat in patterns {
                collect_pattern_refs(&pat.value, refs);
            }
        }
        Pattern::Some(_) => todo!(),
    }
}

fn collect_expr_name_refs(expr: &Node<Expr>, refs: &mut Vec<(NodeId, Path)>) {
    match &expr.value {
        // Arms in alphabetical order by Expr variant for readability
        Expr::Assign(assign) => {
            collect_pattern_refs(&assign.lhs.value, refs);
            collect_expr_name_refs(&assign.rhs, refs);
        }
        Expr::BinOp(bin) => {
            collect_expr_name_refs(&bin.lhs, refs);
            collect_expr_name_refs(&bin.rhs, refs);
        }
        Expr::Block(block) => {
            for stmt in &block.stmts {
                collect_expr_name_refs(stmt, refs);
            }
        }
        Expr::Boxed(boxed) => {
            collect_expr_name_refs(&boxed.inner, refs);
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
        Expr::Continue => {}
        Expr::Curly(curly) => {
            for element in &curly.elements {
                collect_curly_element_refs(element, refs);
            }
        }
        Expr::Dict(dict) => {
            for (key, value) in dict.entries.iter() {
                collect_expr_name_refs(key, refs);
                collect_expr_name_refs(value, refs);
            }
        }
        Expr::DefaultValue(value) => collect_expr_name_refs(value, refs),
        Expr::Deref(deref) => collect_expr_name_refs(&deref.expr, refs),
        Expr::Dot(dot) => {
            collect_expr_name_refs(&dot.lhs, refs);
            refs.push((dot.rhs.id, dot.rhs.value.path.clone()));
        }
        Expr::For(for_expr) => {
            collect_pattern_refs(&for_expr.pat.value, refs);
            collect_expr_name_refs(&for_expr.expr, refs);
            collect_expr_name_refs(&for_expr.body, refs);
        }
        Expr::Func(func) => collect_func_refs(func, refs),
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
        Expr::Missing(_) => {}
        Expr::Name(name) => refs.push((expr.id, name.path.clone())),
        Expr::New(new_expr) => {
            if let Some(count) = &new_expr.count {
                collect_expr_name_refs(count, refs);
            }
        }
        Expr::Paren(value) => collect_expr_name_refs(value, refs),
        Expr::Path(path) => refs.push((expr.id, path.clone())),
        Expr::Pattern(_) => {}
        Expr::Range(range) => {
            collect_expr_name_refs(&range.start, refs);
            collect_expr_name_refs(&range.end, refs);
        }
        Expr::Ref(rf) => {
            collect_expr_name_refs(&rf.expr, refs);
        }
        Expr::Return(value) => {
            if let Some(v) = value {
                collect_expr_name_refs(v, refs);
            }
        }
        Expr::ScopedAccess(scoped_access) => {
            collect_expr_name_refs(&scoped_access.lhs, refs);
            refs.push((scoped_access.rhs.id, scoped_access.rhs.value.path.clone()));
        }
        Expr::Sequence(seq) => {
            for item in &seq.items {
                collect_expr_name_refs(item, refs);
            }
        }
        Expr::Set(set) => {
            for item in set.items.iter() {
                collect_expr_name_refs(item, refs);
            }
        }
        Expr::Some(inner) => collect_expr_name_refs(inner, refs),
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
    }
}

fn collect_curly_element_refs(element: &Node<CurlyElement>, refs: &mut Vec<(NodeId, Path)>) {
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

#[allow(dead_code)]
fn pretty_print_tys<T>(tcx: &TyCtx, ty: &T) -> String
where
    T: Clone + Substitutable + ToString,
{
    tcx.pretty_tys(ty).to_string()
}
