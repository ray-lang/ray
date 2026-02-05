use std::collections::HashMap;

use ray_shared::{node_id::NodeId, pathlib::Path};
use ray_typing::{
    BindingKind, BindingRecord, NodeBinding,
    binding_groups::{BindingId, LegacyBindingGraph},
    env::GlobalEnv,
    types::TyScheme,
};

use crate::ast::{
    Assign, Decl, Expr, FnParam, Func, FuncSig, InfixOp, Module, Name, Node, Pattern as AstPattern,
    WalkItem, WalkScopeKind, walk_module,
};
use crate::sourcemap::SourceMap;

#[derive(Clone, Debug)]
pub struct BindingPassOutput {
    pub bindings: LegacyBindingGraph,
    pub binding_records: HashMap<BindingId, BindingRecord>,
    pub node_bindings: HashMap<NodeId, NodeBinding>,
    pub value_bindings: HashMap<Path, BindingId>,
    pub next_binding: u64,
}

impl BindingPassOutput {
    pub fn empty() -> Self {
        Self {
            bindings: LegacyBindingGraph::new(),
            binding_records: HashMap::new(),
            node_bindings: HashMap::new(),
            value_bindings: HashMap::new(),
            next_binding: 0,
        }
    }
}

pub fn run_binding_pass(
    module: &Module<(), Decl>,
    srcmap: &SourceMap,
    env: &GlobalEnv,
    seed: BindingPassOutput,
) -> BindingPassOutput {
    let mut ctx = BindingPassCtx::new(srcmap, env, seed);
    for item in walk_module(module) {
        ctx.visit_item(item);
    }
    ctx.finish()
}

struct BindingPassCtx<'a> {
    srcmap: &'a SourceMap,
    env: &'a GlobalEnv,
    bindings: LegacyBindingGraph,
    binding_records: HashMap<BindingId, BindingRecord>,
    node_bindings: HashMap<NodeId, NodeBinding>,
    value_bindings: HashMap<Path, BindingId>,
    next_binding: u64,
    scope_stack: Vec<ScopeFrame>,
    binding_stack: Vec<BindingId>,
    pending_pattern_pops: Vec<(NodeId, usize)>,
    pending_pattern_binds: Vec<(NodeId, Vec<BindingId>)>,
}

#[derive(Default)]
struct ScopeFrame {
    locals: HashMap<Path, BindingId>,
    binding_depth: usize,
}

impl<'a> BindingPassCtx<'a> {
    fn new(srcmap: &'a SourceMap, env: &'a GlobalEnv, seed: BindingPassOutput) -> Self {
        let BindingPassOutput {
            bindings,
            binding_records,
            node_bindings,
            value_bindings,
            next_binding,
        } = seed;
        let mut ctx = Self {
            srcmap,
            env,
            bindings,
            binding_records,
            node_bindings,
            value_bindings,
            next_binding,
            scope_stack: Vec::new(),
            binding_stack: Vec::new(),
            pending_pattern_pops: Vec::new(),
            pending_pattern_binds: Vec::new(),
        };
        ctx.scope_stack.push(ScopeFrame::default());
        ctx
    }

    fn finish(self) -> BindingPassOutput {
        BindingPassOutput {
            bindings: self.bindings,
            binding_records: self.binding_records,
            node_bindings: self.node_bindings,
            value_bindings: self.value_bindings,
            next_binding: self.next_binding,
        }
    }

    fn visit_item(&mut self, item: WalkItem<'_>) {
        match item {
            WalkItem::EnterScope(kind) => match kind {
                WalkScopeKind::Function | WalkScopeKind::Block | WalkScopeKind::Closure => {
                    self.push_scope()
                }
                _ => {}
            },
            WalkItem::ExitScope(kind) => match kind {
                WalkScopeKind::Block | WalkScopeKind::Closure | WalkScopeKind::Function => {
                    self.pop_scope()
                }
                _ => {}
            },
            WalkItem::Decl(decl_node) => self.visit_decl(decl_node),
            WalkItem::Func(func_node) => self.record_function(func_node.id, &func_node.value),
            WalkItem::Expr(expr) => self.visit_expr(expr),
            WalkItem::Pattern(node) => {
                while let Some((pattern_id, bindings)) = self.pending_pattern_binds.last().cloned()
                {
                    if pattern_id != node.id {
                        break;
                    }
                    self.pending_pattern_binds.pop();
                    for binding_id in bindings {
                        let Some(record) = self.binding_records.get(&binding_id) else {
                            continue;
                        };
                        let Some(path) = record.path.clone() else {
                            continue;
                        };
                        // Only module-scope bindings participate in the global `value_bindings`
                        // index. Local bindings are resolved via the scope stack; inserting
                        // locals here can cause cross-function collisions for the same path.
                        if self.in_module_scope() {
                            self.value_bindings.insert(path.clone(), binding_id);
                        }
                        self.bind_local(path, binding_id);
                    }
                }
                while let Some((pattern_id, count)) = self.pending_pattern_pops.last().copied() {
                    if pattern_id != node.id {
                        break;
                    }
                    self.pending_pattern_pops.pop();
                    for _ in 0..count {
                        self.pop_binding_context();
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_decl(&mut self, decl_node: &Node<Decl>) {
        match &decl_node.value {
            Decl::Func(func) => self.record_function(decl_node.id, func),
            Decl::FnSig(_) => {}
            Decl::Struct(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) => {}
            Decl::Impl(im) => {
                if let Some(consts) = &im.consts {
                    for assign_node in consts {
                        self.record_assignment(
                            assign_node.id,
                            &assign_node.lhs.value,
                            Some(assign_node.rhs.id),
                        );
                    }
                }
            }
            Decl::Declare(assign) => {
                self.record_assignment(decl_node.id, &assign.lhs.value, Some(assign.rhs.id))
            }
            Decl::Mutable(name, _) => self.record_name_decl(name, true),
            Decl::Name(name, _) => self.record_name_decl(name, false),
            Decl::FileMain(stmts) => {
                for stmt in stmts {
                    self.visit_expr(stmt);
                }
            }
        }
    }

    fn record_function(&mut self, decl_id: NodeId, func: &Func) {
        let sig = &func.sig;
        let parent = self.current_binding();
        let binding = self.new_binding_id();
        let path = Some(sig.path.value.clone());
        self.reserve_binding(binding, decl_id, path.as_ref());

        if func.body.is_some() {
            self.push_binding_context(binding);
            // Record fn params in internal binding system (for dependency tracking)
            // but don't store in BindingKind - the typing phase will populate
            // params with LocalBindingId values from name resolution
            let _params = self.record_fn_params(&sig.params);
        }

        // Use empty params - the typing phase will populate with LocalBindingId
        // values once it has access to resolutions from name resolution
        self.insert_binding_record(
            binding,
            decl_id,
            path,
            BindingKind::Function { params: vec![] },
            sig.ty.clone(),
            parent,
        );

        if func.body.is_some() {
            self.set_binding_body(binding, decl_id);
        }
    }

    fn record_assignment(&mut self, node_id: NodeId, pattern: &AstPattern, rhs: Option<NodeId>) {
        let bindings = self.record_pattern(node_id, pattern);
        if let Some(rhs) = rhs {
            for binding in bindings {
                self.set_binding_body(binding, rhs);
            }
        }
    }

    fn record_name_decl(&mut self, name_node: &Node<Name>, is_mut: bool) {
        let scheme = name_node.value.ty.as_ref().map(|parsed| (**parsed).clone());
        let binding = self.new_binding(
            name_node.id,
            Some(name_node.value.path.clone()),
            BindingKind::Value,
            scheme,
        );
        if is_mut {
            if let Some(record) = self.binding_records.get_mut(&binding) {
                record.is_mut = true;
            }
        }
    }

    fn record_extern(&mut self, extern_decl_id: NodeId, sig_decl_id: NodeId, sig: &FuncSig) {
        let binding = self.new_binding(
            sig_decl_id,
            Some(sig.path.value.clone()),
            BindingKind::Function { params: Vec::new() },
            sig.ty.clone(),
        );
        self.node_bindings
            .insert(extern_decl_id, NodeBinding::Def(binding));
    }

    fn new_binding(
        &mut self,
        node_id: NodeId,
        path: Option<Path>,
        kind: BindingKind,
        scheme: Option<TyScheme>,
    ) -> BindingId {
        let parent = self.current_binding();
        let binding = self.new_binding_id();
        self.insert_binding(binding, node_id, path, kind, scheme, parent);
        binding
    }

    fn insert_binding(
        &mut self,
        binding: BindingId,
        node_id: NodeId,
        path: Option<Path>,
        kind: BindingKind,
        scheme: Option<TyScheme>,
        parent: Option<BindingId>,
    ) {
        self.reserve_binding(binding, node_id, path.as_ref());
        self.insert_binding_record(binding, node_id, path, kind, scheme, parent);
    }

    fn reserve_binding(&mut self, binding: BindingId, node_id: NodeId, path: Option<&Path>) {
        self.bindings.add_binding(binding);
        self.node_bindings
            .insert(node_id, NodeBinding::Def(binding));
        if let Some(p) = path {
            self.value_bindings.insert(p.clone(), binding);
        }
    }

    fn insert_binding_record(
        &mut self,
        binding: BindingId,
        node_id: NodeId,
        path: Option<Path>,
        kind: BindingKind,
        scheme: Option<TyScheme>,
        parent: Option<BindingId>,
    ) {
        let mut record = BindingRecord::new(kind);
        record.path = path;
        record.scheme = scheme;
        record.parent = parent;
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            record.sources.push(src);
        }
        self.binding_records.insert(binding, record);
    }

    fn new_local_binding(
        &mut self,
        node_id: NodeId,
        path: Path,
        kind: BindingKind,
        scheme: Option<TyScheme>,
    ) -> BindingId {
        let binding = self.new_binding_id();
        self.bindings.add_binding(binding);
        self.node_bindings
            .insert(node_id, NodeBinding::Def(binding));
        let mut record = BindingRecord::new(kind);
        record.path = Some(path.clone());
        record.scheme = scheme;
        record.parent = self.current_binding();
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            record.sources.push(src);
        }
        log::debug!(
            "[binding_pass] new local binding for {:?}: {:?}",
            binding,
            record
        );
        self.binding_records.insert(binding, record);
        self.bind_local(path, binding);
        binding
    }

    fn new_local_binding_unbound(
        &mut self,
        node_id: NodeId,
        path: Path,
        kind: BindingKind,
        scheme: Option<TyScheme>,
    ) -> BindingId {
        let binding = self.new_binding_id();
        self.bindings.add_binding(binding);
        self.node_bindings
            .insert(node_id, NodeBinding::Def(binding));
        let mut record = BindingRecord::new(kind);
        record.path = Some(path);
        record.scheme = scheme;
        record.parent = self.current_binding();
        if let Some(src) = self.srcmap.get_by_id(node_id) {
            record.sources.push(src);
        }

        log::debug!(
            "[binding_pass] new local binding (unbound) for {:?}: {:?}",
            binding,
            record
        );
        self.binding_records.insert(binding, record);
        binding
    }

    fn new_binding_id(&mut self) -> BindingId {
        let id = BindingId(self.next_binding);
        self.next_binding += 1;
        id
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(ScopeFrame::default());
    }

    fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            for _ in 0..frame.binding_depth {
                self.binding_stack.pop();
            }
        }
        if self.scope_stack.is_empty() {
            self.scope_stack.push(ScopeFrame::default());
        }
    }

    fn bind_local(&mut self, path: Path, binding: BindingId) {
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.locals.insert(path, binding);
        }
    }

    fn push_binding_context(&mut self, binding: BindingId) {
        self.binding_stack.push(binding);
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.binding_depth += 1;
        }
    }

    fn pop_binding_context(&mut self) {
        if self.binding_stack.pop().is_some() {
            if let Some(frame) = self.scope_stack.last_mut() {
                if frame.binding_depth > 0 {
                    frame.binding_depth -= 1;
                }
            }
        }
    }

    fn current_binding(&self) -> Option<BindingId> {
        self.binding_stack.last().copied()
    }

    fn schedule_pattern_pop(&mut self, node_id: NodeId, count: usize) {
        self.pending_pattern_pops.push((node_id, count));
    }

    fn in_module_scope(&self) -> bool {
        self.scope_stack.len() == 1
    }

    fn resolve_binding(&self, path: &Path) -> Option<BindingId> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(binding) = frame.locals.get(path) {
                return Some(*binding);
            }
        }
        self.value_bindings.get(path).copied()
    }

    fn record_fn_params(&mut self, params: &[Node<FnParam>]) -> Vec<BindingId> {
        let mut out = Vec::with_capacity(params.len());
        for param in params {
            let (path, scheme) = Self::fn_param_binding_info(param);
            let id = self.new_local_binding(param.id, path, BindingKind::Value, scheme);
            out.push(id);
        }
        out
    }

    fn fn_param_binding_info(param: &Node<FnParam>) -> (Path, Option<TyScheme>) {
        match &param.value {
            FnParam::Name(name) => (name.path.clone(), name.ty.as_ref().map(|ty| (**ty).clone())),
            FnParam::DefaultValue(inner, _) => Self::fn_param_binding_info(inner),
            FnParam::Missing { placeholder, .. } => (
                placeholder.path.clone(),
                placeholder.ty.as_ref().map(|ty| (**ty).clone()),
            ),
        }
    }

    fn record_pattern(&mut self, node_id: NodeId, pattern: &AstPattern) -> Vec<BindingId> {
        match pattern {
            AstPattern::Name(name) => {
                let scheme = name.ty.as_ref().map(|ty| (**ty).clone());
                let binding = if self.in_module_scope() {
                    self.new_binding(node_id, Some(name.path.clone()), BindingKind::Value, scheme)
                } else {
                    self.new_local_binding(node_id, name.path.clone(), BindingKind::Value, scheme)
                };
                vec![binding]
            }
            AstPattern::Deref(_) | AstPattern::Dot(_, _) | AstPattern::Index(_, _, _) => Vec::new(),
            AstPattern::Sequence(items) | AstPattern::Tuple(items) => {
                let mut bindings = Vec::new();
                for item in items {
                    bindings.extend(self.record_pattern(item.id, &item.value));
                }
                bindings
            }
            AstPattern::Some(inner) => self.record_pattern(inner.id, &inner.value),
            _ => Vec::new(),
        }
    }

    fn record_pattern_unbound(&mut self, node_id: NodeId, pattern: &AstPattern) -> Vec<BindingId> {
        match pattern {
            AstPattern::Name(name) => {
                let scheme = name.ty.as_ref().map(|ty| (**ty).clone());
                let binding = if self.in_module_scope() {
                    self.new_binding(node_id, Some(name.path.clone()), BindingKind::Value, scheme)
                } else {
                    self.new_local_binding_unbound(
                        node_id,
                        name.path.clone(),
                        BindingKind::Value,
                        scheme,
                    )
                };
                vec![binding]
            }
            AstPattern::Sequence(items) | AstPattern::Tuple(items) => {
                let mut bindings = Vec::new();
                for item in items {
                    bindings.extend(self.record_pattern_unbound(item.id, &item.value));
                }
                bindings
            }
            AstPattern::Some(inner) => self.record_pattern_unbound(inner.id, &inner.value),
            AstPattern::Deref(_)
            | AstPattern::Dot(_, _)
            | AstPattern::Index(_, _, _)
            | AstPattern::Missing(_) => Vec::new(),
        }
    }

    fn set_binding_body(&mut self, binding: BindingId, expr: NodeId) {
        if let Some(record) = self.binding_records.get_mut(&binding) {
            record.body_expr = Some(expr);
        }
    }

    fn record_name_use(&mut self, node_id: NodeId, path: &Path) {
        if let Some(target) = self.resolve_binding(path) {
            self.node_bindings
                .entry(node_id)
                .or_insert(NodeBinding::Use(target));
            if let Some(source) = self.current_binding() {
                if source != target {
                    self.bindings.add_edge(source, target);
                }
            }
        }
    }

    fn record_binding_use_with_edge(&mut self, node_id: NodeId, target: BindingId) {
        self.node_bindings
            .entry(node_id)
            .or_insert(NodeBinding::Use(target));
        if let Some(source) = self.current_binding() {
            if source != target {
                self.bindings.add_edge(source, target);
            }
        }
    }

    fn is_mut_binding(&self, binding: BindingId) -> bool {
        self.binding_records
            .get(&binding)
            .map(|record| record.is_mut)
            .unwrap_or(false)
    }

    fn resolve_mut_slot_assignment_target(&self, assign: &Assign) -> Option<BindingId> {
        let AstPattern::Name(name) = &assign.lhs.value else {
            return None;
        };
        let target = self.resolve_binding(&name.path)?;
        if !self.is_mut_binding(target) {
            return None;
        }
        Some(target)
    }

    fn record_lvalue_pattern_uses(&mut self, pattern: &Node<AstPattern>) {
        match &pattern.value {
            AstPattern::Deref(name) => {
                self.record_name_use(name.id, &name.path);
            }
            AstPattern::Dot(lhs, _) => self.record_lvalue_pattern_uses(lhs.as_ref()),
            AstPattern::Index(lhs, index, _) => {
                self.record_lvalue_pattern_uses(lhs.as_ref());
                self.visit_expr(index.as_ref());
            }
            AstPattern::Sequence(items) | AstPattern::Tuple(items) => {
                for item in items {
                    self.record_lvalue_pattern_uses(item);
                }
            }
            AstPattern::Some(inner) => self.record_lvalue_pattern_uses(inner.as_ref()),
            AstPattern::Name(name) => self.record_name_use(pattern.id, &name.path),
            AstPattern::Missing(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &Node<Expr>) {
        match &expr.value {
            Expr::Assign(assign) => {
                if let Some(target) = self.resolve_mut_slot_assignment_target(assign) {
                    self.record_binding_use_with_edge(assign.lhs.id, target);
                    return;
                }

                // Create fresh binding ids for the LHS, but defer binding them
                // into the local scope until after the RHS has been walked.
                // This ensures RHS name uses resolve to the pre-assignment
                // binding(s), while dependency edges still originate from the
                // new binding(s) via `push_binding_context`.
                let bindings = self.record_pattern_unbound(assign.lhs.id, &assign.lhs.value);
                if !bindings.is_empty() {
                    for binding in &bindings {
                        self.set_binding_body(*binding, assign.rhs.id);
                        if assign.is_mut {
                            if let Some(record) = self.binding_records.get_mut(binding) {
                                record.is_mut = true;
                            }
                        }
                    }
                    let count = bindings.len();
                    self.schedule_pattern_pop(assign.lhs.id, count);
                    self.pending_pattern_binds
                        .push((assign.lhs.id, bindings.clone()));
                    for binding in bindings {
                        self.push_binding_context(binding);
                    }
                }

                // Record uses of the lvalue (e.g. `*ptr = ...`, `p.x = ...`, `l[i] = ...`).
                if !matches!(assign.lhs.value, AstPattern::Name(_)) {
                    self.record_lvalue_pattern_uses(&assign.lhs);
                }
            }
            Expr::Closure(closure) => {
                self.record_closure_params(&closure.args.items);
            }
            Expr::For(for_expr) => {
                self.record_pattern(for_expr.pat.id, &for_expr.pat.value);
            }
            Expr::Func(func) => {
                if func.body.is_some() {
                    self.record_fn_params(&func.sig.params);
                }
            }
            Expr::Name(name) => {
                if let Some(target) = self.resolve_binding(&name.path) {
                    self.node_bindings
                        .entry(expr.id)
                        .or_insert(NodeBinding::Use(target));
                    if let Some(source) = self.current_binding() {
                        if source != target {
                            self.bindings.add_edge(source, target);
                        }
                    }
                }
            }
            Expr::Path(segments) => {
                // Convert Vec<Node<String>> to Path for binding resolution
                let path = Path::from(segments.iter().map(|s| s.value.clone()).collect::<Vec<_>>());
                if let Some(target) = self.resolve_binding(&path) {
                    self.node_bindings
                        .entry(expr.id)
                        .or_insert(NodeBinding::Use(target));
                    if let Some(source) = self.current_binding() {
                        if source != target {
                            self.bindings.add_edge(source, target);
                        }
                    }
                }
            }
            Expr::ScopedAccess(scoped_access) => {
                // Only record binding edges for type-qualified scoped access
                // like `dict['k,'v]::with_capacity` for now.
                if let Expr::Type(ty) = &scoped_access.lhs.value {
                    let base = ty.value().mono().get_path().without_type_args();
                    let member = scoped_access
                        .rhs
                        .value
                        .path
                        .name()
                        .unwrap_or_else(|| scoped_access.rhs.value.to_string());
                    let path = base.append(member);
                    if let Some(target) = self.resolve_binding(&path) {
                        self.node_bindings
                            .entry(expr.id)
                            .or_insert(NodeBinding::Use(target));
                        if let Some(source) = self.current_binding() {
                            if source != target {
                                self.bindings.add_edge(source, target);
                            }
                        }
                    }
                }
            }
            Expr::BinOp(binop) => {
                self.record_infix_op_use(&binop.op);
            }
            _ => {}
        }
    }

    fn record_infix_op_use(&mut self, op: &Node<InfixOp>) {
        let Some((method_fqn, _trait_fqn)) = self.env.lookup_infix_op(op.value.as_str()) else {
            return;
        };
        let Some(target) = self.resolve_binding(method_fqn) else {
            return;
        };

        self.node_bindings
            .entry(op.id)
            .or_insert(NodeBinding::Use(target));

        if let Some(source) = self.current_binding() {
            if source != target {
                self.bindings.add_edge(source, target);
            }
        }
    }

    fn record_closure_params(&mut self, params: &[Node<Expr>]) {
        for param in params {
            if let Expr::Name(name) = &param.value {
                let scheme = name.ty.as_ref().map(|ty| (**ty).clone());
                self.new_local_binding(param.id, name.path.clone(), BindingKind::Value, scheme);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Assign, Block, Closure, Expr, For, Func, If, Impl, InfixOp, Literal, Sequence, While,
    };
    use ray_shared::def::DefId;
    use ray_shared::file_id::FileId;
    use ray_shared::node_id::{NodeId, NodeIdGuard};
    use ray_shared::pathlib::{FilePath, Path};
    use ray_shared::span::{Source, Span, parsed::Parsed};
    use ray_shared::ty::Ty;
    use ray_typing::env::GlobalEnv;
    use ray_typing::types::TyScheme;

    /// Set up a DefId context for tests that create nodes.
    fn test_def_context() -> NodeIdGuard {
        NodeId::enter_def(DefId::new(FileId(0), 0))
    }

    fn test_source() -> Source {
        Source::new(
            FilePath::from("test.ray"),
            Span::new(),
            Path::new(),
            Path::new(),
        )
    }

    fn seed_src<T>(srcmap: &mut SourceMap, node: &Node<T>) {
        srcmap.set_src(node, test_source());
    }

    fn test_module(decls: Vec<Node<Decl>>) -> Module<(), Decl> {
        Module {
            path: Path::from("test"),
            stmts: vec![],
            decls,
            imports: vec![],
            import_stmts: vec![],
            submodules: vec![],
            doc_comment: None,
            root_filepath: FilePath::from("test.ray"),
            filepaths: vec![FilePath::from("test.ray")],
            is_lib: false,
        }
    }

    #[test]
    fn records_use_bindings_for_name_exprs() {
        let _guard = test_def_context();
        let local_pattern = Node::new(AstPattern::Name(Name::new("x")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: local_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_expr = Node::new(Expr::Assign(assign));
        let use_expr = Node::new(Expr::Name(Name::new("x")));

        let body = Node::new(Expr::Block(Block {
            stmts: vec![assign_expr.clone(), use_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::f")), vec![], body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &local_pattern);
        seed_src(&mut srcmap, &rhs_expr);
        seed_src(&mut srcmap, &assign_expr);
        seed_src(&mut srcmap, &use_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());

        let local_binding = match output.node_bindings.get(&local_pattern.id) {
            Some(NodeBinding::Def(binding)) => *binding,
            Some(NodeBinding::Use(_)) => panic!("expected def binding for local pattern"),
            None => panic!("local pattern binding missing"),
        };
        let use_binding = match output.node_bindings.get(&use_expr.id) {
            Some(NodeBinding::Use(binding)) => *binding,
            Some(NodeBinding::Def(_)) => panic!("expected use binding for name expr"),
            None => panic!("name expr binding missing"),
        };
        assert_eq!(use_binding, local_binding);
    }

    #[test]
    fn records_closure_and_inline_function_params() {
        let _guard = test_def_context();
        let closure_param = Node::new(Expr::Name(Name::new("closure_param")));
        let closure = Closure {
            args: Sequence::new(vec![closure_param.clone()]),
            body: Box::new(Node::new(Expr::Literal(Literal::Bool(true)))),
            arrow_span: None,
            curly_spans: None,
        };
        let closure_expr = Node::new(Expr::Closure(closure));

        let inline_param = Node::new(FnParam::Name(Name::new("inline_param")));
        let inline_body_expr = Node::new(Expr::Literal(Literal::Bool(false)));
        let inline_body_block = Node::new(Expr::Block(Block {
            stmts: vec![inline_body_expr.clone()],
        }));
        let inline_func = Func::new(
            Node::new(Path::from("pkg::inline")),
            vec![inline_param.clone()],
            inline_body_block,
        );
        let inline_expr = Node::new(Expr::Func(inline_func));

        let outer_body = Node::new(Expr::Block(Block {
            stmts: vec![closure_expr.clone(), inline_expr.clone()],
        }));
        let outer_func = Func::new(Node::new(Path::from("pkg::outer")), vec![], outer_body);
        let outer_decl = Node::new(Decl::Func(outer_func));

        let module = test_module(vec![outer_decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &outer_decl);
        seed_src(&mut srcmap, &closure_param);
        seed_src(&mut srcmap, &closure_expr);
        seed_src(&mut srcmap, &inline_param);
        seed_src(&mut srcmap, &inline_expr);
        seed_src(&mut srcmap, &inline_body_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());

        let closure_binding = output
            .node_bindings
            .get(&closure_param.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("closure param binding missing");
        let closure_record = output
            .binding_records
            .get(&closure_binding)
            .expect("closure param record missing");
        assert_eq!(
            closure_record
                .path
                .as_ref()
                .map(|p| p.to_string())
                .as_deref(),
            Some("closure_param")
        );

        let inline_binding = output
            .node_bindings
            .get(&inline_param.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("inline param binding missing");
        let inline_record = output
            .binding_records
            .get(&inline_binding)
            .expect("inline param record missing");
        assert_eq!(
            inline_record
                .path
                .as_ref()
                .map(|p| p.to_string())
                .as_deref(),
            Some("inline_param")
        );
    }

    #[test]
    fn records_function_params_and_locals() {
        let _guard = test_def_context();
        let param = Node::new(FnParam::Name(Name::new("param")));
        let local_pattern = Node::new(AstPattern::Name(Name::new("local")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: local_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_stmt = Node::new(Expr::Assign(assign));
        let block_expr = Node::new(Expr::Block(Block {
            stmts: vec![assign_stmt.clone()],
        }));
        let func = Func::new(
            Node::new(Path::from("pkg::func")),
            vec![param.clone()],
            block_expr,
        );
        let func_decl = Node::new(Decl::Func(func));

        let module = test_module(vec![func_decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &func_decl);
        seed_src(&mut srcmap, &param);
        seed_src(&mut srcmap, &local_pattern);
        seed_src(&mut srcmap, &assign_stmt);
        seed_src(&mut srcmap, &rhs_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());

        let func_binding = output
            .node_bindings
            .get(&func_decl.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("function binding recorded");
        let func_record = output
            .binding_records
            .get(&func_binding)
            .expect("has binding record");
        assert_eq!(func_record.body_expr, Some(func_decl.id));
        match &func_record.kind {
            BindingKind::Function { params } => {
                // Params are now populated by the typing phase from resolutions,
                // not by the binding pass. The binding pass sets params to empty.
                assert!(
                    params.is_empty(),
                    "expected empty params in binding pass, typing phase populates"
                );
            }
            other => panic!("expected function binding, found {:?}", other),
        }

        let local_binding = output
            .node_bindings
            .get(&local_pattern.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("local binding recorded");
        let local_record = output
            .binding_records
            .get(&local_binding)
            .expect("local binding record");
        assert_eq!(local_record.body_expr, Some(rhs_expr.id));
        assert_eq!(
            local_record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("local")
        );
        assert!(matches!(local_record.kind, BindingKind::Value));
    }

    #[test]
    fn records_destructuring_declares() {
        let _guard = test_def_context();
        let first = Node::new(AstPattern::Name(Name::new("first")));
        let second = Node::new(AstPattern::Name(Name::new("second")));
        let tuple = Node::new(AstPattern::Tuple(vec![first.clone(), second.clone()]));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: tuple.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let decl = Node::new(Decl::Declare(assign));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &first);
        seed_src(&mut srcmap, &second);
        seed_src(&mut srcmap, &rhs_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());

        for (node, name) in [(&first, "first"), (&second, "second")] {
            let binding = output
                .node_bindings
                .get(&node.id)
                .copied()
                .and_then(|b| match b {
                    NodeBinding::Def(id) => Some(id),
                    NodeBinding::Use(_) => None,
                })
                .unwrap_or_else(|| panic!("missing binding for {}", name));
            let record = output
                .binding_records
                .get(&binding)
                .expect("binding record missing");
            assert_eq!(
                record.path.as_ref().map(|p| p.to_string()).as_deref(),
                Some(name)
            );
            assert!(matches!(record.kind, BindingKind::Value));
        }
    }

    #[test]
    fn records_for_pattern_bindings() {
        let _guard = test_def_context();
        let pat = Node::new(AstPattern::Name(Name::new("item")));
        let iter_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let body_block = Node::new(Expr::Block(Block { stmts: vec![] }));
        let for_expr = Node::new(Expr::For(For {
            pat: pat.clone(),
            expr: Box::new(iter_expr.clone()),
            body: Box::new(body_block.clone()),
            for_span: Span::new(),
            in_span: Span::new(),
        }));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![for_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::for_fn")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &pat);
        seed_src(&mut srcmap, &iter_expr);
        seed_src(&mut srcmap, &body_block);
        seed_src(&mut srcmap, &for_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&pat.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("for-loop pattern binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("pattern binding record missing");
        assert_eq!(
            record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("item")
        );
        assert!(matches!(record.kind, BindingKind::Value));
    }

    #[test]
    fn records_while_assignment_bindings() {
        let _guard = test_def_context();
        let pat = Node::new(AstPattern::Name(Name::new("loop_var")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: pat.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let cond_expr = Node::new(Expr::Assign(assign));
        let body_block = Node::new(Expr::Block(Block { stmts: vec![] }));
        let while_expr = Node::new(Expr::While(While {
            cond: Box::new(cond_expr.clone()),
            body: Box::new(body_block.clone()),
            while_span: Span::new(),
        }));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![while_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::while_fn")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &pat);
        seed_src(&mut srcmap, &rhs_expr);
        seed_src(&mut srcmap, &cond_expr);
        seed_src(&mut srcmap, &body_block);
        seed_src(&mut srcmap, &while_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&pat.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("while-assignment binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("binding record missing");
        assert_eq!(
            record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("loop_var")
        );
        assert!(matches!(record.kind, BindingKind::Value));
    }

    #[test]
    fn records_if_assignment_bindings() {
        let _guard = test_def_context();
        let pat = Node::new(AstPattern::Name(Name::new("if_var")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: pat.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let cond_expr = Node::new(Expr::Assign(assign));
        let then_block = Node::new(Expr::Block(Block { stmts: vec![] }));
        let if_expr = Node::new(Expr::If(If {
            cond: Box::new(cond_expr.clone()),
            then: Box::new(then_block.clone()),
            els: None,
        }));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![if_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::if_fn")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &pat);
        seed_src(&mut srcmap, &rhs_expr);
        seed_src(&mut srcmap, &cond_expr);
        seed_src(&mut srcmap, &then_block);
        seed_src(&mut srcmap, &if_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&pat.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("if-assignment binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("binding record missing");
        assert_eq!(
            record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("if_var")
        );
        assert!(matches!(record.kind, BindingKind::Value));
    }

    #[test]
    fn records_impl_const_bindings() {
        let _guard = test_def_context();
        let const_pattern = Node::new(AstPattern::Name(Name::new("IMPL_CONST")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: const_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let const_node = Node::new(assign);

        let impl_decl = Node::new(Decl::Impl(Impl {
            ty: Parsed::new(Ty::bool(), test_source()),
            qualifiers: vec![],
            externs: None,
            funcs: None,
            consts: Some(vec![const_node.clone()]),
            is_object: false,
        }));

        let module = test_module(vec![impl_decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &impl_decl);
        seed_src(&mut srcmap, &const_pattern);
        seed_src(&mut srcmap, &rhs_expr);
        seed_src(&mut srcmap, &const_node);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&const_node.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("impl const binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("impl const record missing");
        assert_eq!(
            record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("IMPL_CONST")
        );
        assert!(matches!(record.kind, BindingKind::Value));
    }

    #[test]
    fn records_mutable_and_named_decls_with_schemes() {
        let _guard = test_def_context();
        let scheme = TyScheme::from_mono(Ty::bool());
        let parsed = Parsed::new(scheme.clone(), test_source());
        let mutable_name = Node::new(Name::typed("pkg::MUTABLE", parsed.clone()));
        let named_name = Node::new(Name::typed("pkg::CONST", parsed));

        let mutable_decl = Node::new(Decl::Mutable(mutable_name.clone(), vec![]));
        let named_decl = Node::new(Decl::Name(named_name.clone(), vec![]));

        let module = test_module(vec![mutable_decl.clone(), named_decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &mutable_decl);
        seed_src(&mut srcmap, &named_decl);
        seed_src(&mut srcmap, &mutable_name);
        seed_src(&mut srcmap, &named_name);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        for node in [mutable_name, named_name] {
            let binding = output
                .node_bindings
                .get(&node.id)
                .copied()
                .and_then(|b| match b {
                    NodeBinding::Def(id) => Some(id),
                    NodeBinding::Use(_) => None,
                })
                .unwrap_or_else(|| panic!("binding missing for {}", node.value.path));
            let record = output
                .binding_records
                .get(&binding)
                .expect("binding record missing");
            assert_eq!(
                record.path.as_ref().map(|p| p.to_string()),
                Some(node.value.path.to_string())
            );
            assert!(
                matches!(record.kind, BindingKind::Value),
                "expected value binding"
            );
            assert!(record.scheme.is_some());
        }
    }

    #[test]
    fn records_mutable_and_named_decls_without_schemes() {
        let _guard = test_def_context();
        let mutable_name = Node::new(Name::new("pkg::UNANNOTATED_MUT"));
        let named_name = Node::new(Name::new("pkg::UNANNOTATED_CONST"));

        let mutable_decl = Node::new(Decl::Mutable(mutable_name.clone(), vec![]));
        let named_decl = Node::new(Decl::Name(named_name.clone(), vec![]));

        let module = test_module(vec![mutable_decl.clone(), named_decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &mutable_decl);
        seed_src(&mut srcmap, &named_decl);
        seed_src(&mut srcmap, &mutable_name);
        seed_src(&mut srcmap, &named_name);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        for node in [mutable_name, named_name] {
            let binding = output
                .node_bindings
                .get(&node.id)
                .copied()
                .and_then(|b| match b {
                    NodeBinding::Def(id) => Some(id),
                    NodeBinding::Use(_) => None,
                })
                .unwrap_or_else(|| panic!("binding missing for {}", node.value.path));
            let record = output
                .binding_records
                .get(&binding)
                .expect("binding record missing");
            assert!(
                record.scheme.is_none(),
                "scheme should be None for unannotated decls"
            );
            assert!(matches!(record.kind, BindingKind::Value));
        }
    }

    #[test]
    fn records_nested_patterns_inside_closures() {
        let _guard = test_def_context();
        let inner_a = Node::new(AstPattern::Name(Name::new("a")));
        let inner_b = Node::new(AstPattern::Name(Name::new("b")));
        let tuple_pattern = Node::new(AstPattern::Tuple(vec![inner_a.clone(), inner_b.clone()]));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: tuple_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_expr = Node::new(Expr::Assign(assign));
        let closure = Closure {
            args: Sequence::new(vec![]),
            body: Box::new(assign_expr.clone()),
            arrow_span: None,
            curly_spans: None,
        };
        let closure_expr = Node::new(Expr::Closure(closure));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![closure_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::captures")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &closure_expr);
        seed_src(&mut srcmap, &tuple_pattern);
        seed_src(&mut srcmap, &inner_a);
        seed_src(&mut srcmap, &inner_b);
        seed_src(&mut srcmap, &assign_expr);
        seed_src(&mut srcmap, &rhs_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        for node in [inner_a, inner_b] {
            let binding = output
                .node_bindings
                .get(&node.id)
                .copied()
                .and_then(|b| match b {
                    NodeBinding::Def(id) => Some(id),
                    NodeBinding::Use(_) => None,
                })
                .unwrap_or_else(|| panic!("closure binding missing for {:?}", node.value));
            let record = output
                .binding_records
                .get(&binding)
                .expect("closure binding record missing");
            assert!(matches!(record.kind, BindingKind::Value));
        }
    }

    #[test]
    fn records_block_local_bindings_without_global_paths() {
        let _guard = test_def_context();
        let local_pattern = Node::new(AstPattern::Name(Name::new("pkg::locals::local_var")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: local_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_expr = Node::new(Expr::Assign(assign));
        let inner_block = Node::new(Expr::Block(Block {
            stmts: vec![assign_expr.clone()],
        }));
        let outer_block = Node::new(Expr::Block(Block {
            stmts: vec![inner_block.clone()],
        }));
        let func = Func::new(
            Node::new(Path::from("pkg::locals")),
            vec![],
            outer_block.clone(),
        );
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &inner_block);
        seed_src(&mut srcmap, &outer_block);
        seed_src(&mut srcmap, &local_pattern);
        seed_src(&mut srcmap, &assign_expr);
        seed_src(&mut srcmap, &rhs_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&local_pattern.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("local block binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("local block record missing");
        assert!(matches!(record.kind, BindingKind::Value));
    }

    #[test]
    fn records_some_patterns_in_declares() {
        let _guard = test_def_context();
        let inner = Node::new(AstPattern::Name(Name::new("inner")));
        let some_pattern = Node::new(AstPattern::Some(Box::new(inner.clone())));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: some_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: InfixOp::Assign,
            op_span: Span::new(),
        };
        let decl = Node::new(Decl::Declare(assign));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &some_pattern);
        seed_src(&mut srcmap, &inner);
        seed_src(&mut srcmap, &rhs_expr);

        let env = GlobalEnv::default();
        let output = run_binding_pass(&module, &srcmap, &env, BindingPassOutput::empty());
        let binding = output
            .node_bindings
            .get(&inner.id)
            .copied()
            .and_then(|b| match b {
                NodeBinding::Def(id) => Some(id),
                NodeBinding::Use(_) => None,
            })
            .expect("inner binding missing");
        let record = output
            .binding_records
            .get(&binding)
            .expect("inner record missing");
        assert_eq!(
            record.path.as_ref().map(|p| p.to_string()).as_deref(),
            Some("inner")
        );
        assert!(matches!(record.kind, BindingKind::Value));
    }
}
