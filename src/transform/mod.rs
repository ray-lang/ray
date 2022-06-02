use std::collections::{HashMap, HashSet};

use crate::{
    ast::{self, Decl, Expr, Literal, LowerAST, Module, Node, Path},
    errors::RayError,
    span::{Source, SourceMap, Span},
    typing::TyCtx,
};

type SourceModule = Module<Expr, Decl>;

pub fn combine(
    module_path: &Path,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    lib_set: &HashSet<Path>,
    tcx: &mut TyCtx,
) -> Result<(Module<(), Decl>, SourceMap, HashMap<Path, Vec<Path>>), RayError> {
    let module = modules.remove(module_path).unwrap();
    let mut srcmap = srcmaps.remove(module_path).unwrap();
    let mut new_module = Module::new_from::<(), Decl>(&module);
    let mut scope_map = HashMap::new();
    let (mut stmts, mut decls) = get_root(
        module,
        &mut srcmap,
        modules,
        srcmaps,
        &mut scope_map,
        lib_set,
        tcx,
    )?;

    let filepath = new_module.root_filepath.clone();

    let mut span = Span::new();
    if let Some(first) = stmts.first() {
        span.start = srcmap.span_of(first).start;
    }

    if let Some(last) = stmts.last() {
        span.end = srcmap.span_of(last).end;
    }

    let end_node = Node::new(Expr::Literal(Literal::Unit));
    srcmap.set_src(
        &end_node,
        Source {
            filepath: filepath.clone(),
            ..Default::default()
        },
    );
    stmts.push(end_node);

    let body = Node::new(Expr::Block(ast::Block {
        stmts,
        is_top_level: true,
    }));
    srcmap.set_src(
        &body,
        Source::new(filepath.clone(), span, Path::new(), module_path.clone()),
    );

    // create a "main" function for the stmts
    let main_path = module_path.append("main");
    let main_decl = Node::new(Decl::Func(ast::Func::new(main_path, vec![], body)));
    srcmap.set_src(
        &main_decl,
        Source::new(filepath.clone(), span, Path::new(), module_path.clone()),
    );
    decls.push(main_decl);

    new_module.decls = decls;
    Ok((new_module, srcmap, scope_map))
}

fn get_root(
    module: SourceModule,
    srcmap: &mut SourceMap,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    scope_map: &mut HashMap<Path, Vec<Path>>,
    lib_set: &HashSet<Path>,
    tcx: &mut TyCtx,
) -> Result<(Vec<Node<Expr>>, Vec<Node<Decl>>), RayError> {
    let (mut stmts, mut decls) = collect(module, srcmap, modules, srcmaps, scope_map, lib_set)?;
    // sorting it by kind will allow a certain order to the collection
    decls.sort();

    for decl in decls.iter_mut() {
        decl.lower(srcmap, scope_map, tcx)?;
    }

    for stmt in stmts.iter_mut() {
        stmt.lower(srcmap, scope_map, tcx)?;
    }

    Ok((stmts, decls))
}

fn collect(
    module: SourceModule,
    srcmap: &mut SourceMap,
    modules: &mut HashMap<Path, SourceModule>,
    srcmaps: &mut HashMap<Path, SourceMap>,
    scope_map: &mut HashMap<Path, Vec<Path>>,
    lib_set: &HashSet<Path>,
) -> Result<(Vec<Node<Expr>>, Vec<Node<Decl>>), RayError> {
    let mut stmts = vec![];
    let mut decls = vec![];

    let mut scopes = vec![module.path.clone()];
    scopes.extend(module.imports.clone());
    scope_map.insert(module.path.clone(), scopes);
    for import_path in module.imports.iter() {
        if lib_set.contains(import_path) {
            continue;
        }

        let imported_module = modules.remove(import_path).unwrap();
        let mut imported_srcmap = srcmaps.remove(import_path).unwrap();
        let (imported_stmts, imported_decls) = collect(
            imported_module,
            &mut imported_srcmap,
            modules,
            srcmaps,
            scope_map,
            lib_set,
        )?;
        srcmap.extend(imported_srcmap);
        decls.extend(imported_decls);
        stmts.extend(imported_stmts);
    }

    decls.extend(module.decls);
    stmts.extend(module.stmts);
    Ok((stmts, decls))
}
