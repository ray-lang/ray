use std::collections::{HashMap, HashSet};

use ray_shared::span::{Source, Span};
use ray_shared::{
    collections::{namecontext::NameContext, nametree::Scope},
    node_id::NodeId,
    pathlib::{FilePath, Path},
};
use ray_typing::tyctx::TyCtx;

use crate::{
    ast::{self, AstLowerCtx, Decl, Expr, Literal, LowerAST, Module, Node},
    errors::RayError,
    sema::{NameResolve, ResolveContext},
    sourcemap::SourceMap,
};

type SourceModule = Module<Expr, Decl>;
pub struct CombineResult {
    pub module: Module<(), Decl>,
    pub srcmap: SourceMap,
    pub tcx: TyCtx,
    pub ncx: NameContext,
}

struct ModuleCombiner {
    base_module_path: Path,
    modules: HashMap<Path, SourceModule>,
    srcmaps: HashMap<Path, SourceMap>,
    module_set: HashSet<Path>,
    scope_map: HashMap<Path, Vec<Scope>>,
    tcx: TyCtx,
    ncx: NameContext,
    errors: Vec<RayError>,
}

impl ModuleCombiner {
    fn combine(mut self) -> Result<CombineResult, Vec<RayError>> {
        let (module, mut srcmap) = self.get_base_module();
        let mut new_module = Module::new_from::<(), Decl>(&module);
        let mut modules = vec![];
        self.collect(module, &mut srcmap, &mut modules)?;
        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        for module in modules {
            let _node_id_namespace = NodeId::enter_namespace(&module.path);

            new_module.decls.extend(module.decls);
            let main_decl = self.create_main_func(
                &module.path,
                &module.root_filepath,
                module.stmts,
                &mut srcmap,
            )?;
            new_module.decls.push(main_decl);
        }

        // sorting it by kind will allow a certain order to the collection
        new_module.decls.sort();

        // process name resolution
        let mut ctx = ResolveContext::new(&mut self.ncx, &mut srcmap, &self.scope_map);
        new_module.resolve_names(&mut ctx)?;

        // lower the declarations for the current module
        let mut ctx = self.get_lower_ctx(&mut srcmap);
        for decl in new_module.decls.iter_mut() {
            let src = ctx.srcmap().get(decl);
            let _node_id_namespace = NodeId::enter_namespace(&src.src_module);
            decl.lower(&mut ctx)?;
        }

        Ok(CombineResult {
            module: new_module,
            srcmap,
            tcx: self.tcx,
            ncx: self.ncx,
        })
    }

    fn collect(
        &mut self,
        module: SourceModule,
        parent_srcmap: &mut SourceMap,
        modules: &mut Vec<SourceModule>,
    ) -> Result<(), Vec<RayError>> {
        log::debug!("collecting declarations from module: {}", module.path);

        // clone paths for later use
        self.module_set.insert(module.path.clone());

        // extend the scope map with the module path and import paths
        // note: submodule paths aren't added unless they are imported
        let mut scopes = vec![Scope::from(module.path.clone())];
        scopes.extend(module.imports.clone());
        log::debug!("scopes for module {}: {:?}", module.path, scopes);
        self.scope_map.insert(module.path.clone(), scopes);

        for module_path in module
            .imports
            .iter()
            .map(|scope| &scope.path)
            .chain(module.submodules.iter())
        {
            self.extend_from_submodule(module_path, parent_srcmap, modules)?;
        }

        modules.push(module);
        Ok(())
    }

    fn extend_from_submodule(
        &mut self,
        module_path: &Path,
        parent_srcmap: &mut SourceMap,
        modules: &mut Vec<SourceModule>,
    ) -> Result<(), Vec<RayError>> {
        if self.module_set.contains(module_path) {
            log::debug!("module has already been collected: {}", module_path);

            // make sure the source map has been removed and put in the parent
            if let Some(srcmap) = self.srcmaps.remove(module_path) {
                parent_srcmap.extend_with(srcmap);
            }
            return Ok(());
        }

        let (sub_module, sub_srcmap) = self.get_module(module_path);
        parent_srcmap.extend_with(sub_srcmap);
        self.collect(sub_module, parent_srcmap, modules)?;
        Ok(())
    }

    fn create_main_func(
        &mut self,
        module_path: &Path,
        filepath: &FilePath,
        mut stmts: Vec<Node<Expr>>,
        srcmap: &mut SourceMap,
    ) -> Result<Node<Decl>, RayError> {
        let _node_id_namespace = NodeId::enter_namespace(module_path);

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

        let body = Node::new(Expr::Block(ast::Block::new(stmts)));
        srcmap.set_src(
            &body,
            Source::new(filepath.clone(), span, Path::new(), module_path.clone()),
        );

        // create a "_ray_main" function for the stmts
        let main_path = module_path.append("_ray_main");
        let main_path_node = Node::new(main_path);
        let main_decl = Node::new(Decl::Func(ast::Func::new(main_path_node, vec![], body)));
        srcmap.set_src(
            &main_decl,
            Source::new(filepath.clone(), span, Path::new(), module_path.clone()),
        );
        Ok(main_decl)
    }

    fn get_base_module(&mut self) -> (SourceModule, SourceMap) {
        let module = self.modules.remove(&self.base_module_path).unwrap();
        let srcmap = self.srcmaps.remove(&self.base_module_path).unwrap();
        (module, srcmap)
    }

    fn get_module(&mut self, module_path: &Path) -> (SourceModule, SourceMap) {
        let module = self.modules.remove(module_path).unwrap();
        let srcmap = self.srcmaps.remove(module_path).unwrap();
        (module, srcmap)
    }

    fn get_lower_ctx<'a>(&'a mut self, srcmap: &'a mut SourceMap) -> AstLowerCtx<'a> {
        AstLowerCtx::new(
            srcmap,
            &mut self.scope_map,
            &mut self.tcx,
            &mut self.ncx,
            &mut self.errors,
        )
    }
}

pub fn combine(
    module_path: &Path,
    modules: HashMap<Path, SourceModule>,
    srcmaps: HashMap<Path, SourceMap>,
    lib_set: HashSet<Path>,
    tcx: TyCtx,
    ncx: NameContext,
) -> Result<CombineResult, Vec<RayError>> {
    let combiner = ModuleCombiner {
        base_module_path: module_path.clone(),
        modules,
        srcmaps,
        module_set: lib_set,
        tcx,
        ncx,
        scope_map: HashMap::new(),
        errors: Vec::new(),
    };

    combiner.combine()
}
