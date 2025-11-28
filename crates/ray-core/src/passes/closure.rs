use std::collections::{HashMap, HashSet};

use ray_shared::node_id::NodeId;
use ray_shared::pathlib::Path;
use ray_typing::NodeBinding;
use ray_typing::binding_groups::BindingId;

use crate::ast::{Closure, Decl, Expr, FnParam, Module, WalkItem, WalkScopeKind, walk_module};
use crate::passes::binding::BindingPassOutput;
use crate::sourcemap::SourceMap;

/// Information about a single closure expression.
#[derive(Debug, Default, Clone)]
pub struct ClosureInfo {
    pub parent_binding: BindingId,
    pub captures: Vec<BindingId>,
    pub body_expr: Option<NodeId>,
    pub closure_expr: NodeId,
}

#[derive(Debug, Default, Clone)]
pub struct ClosurePassOutput {
    pub closures: Vec<ClosureInfo>,
}

pub fn run_closure_pass(
    module: &Module<(), Decl>,
    _srcmap: &SourceMap,
    bindings: &BindingPassOutput,
) -> ClosurePassOutput {
    let mut ctx = ClosurePassCtx::new(bindings);
    for item in walk_module(module) {
        ctx.visit_item(item);
    }
    ClosurePassOutput {
        closures: ctx.closures,
    }
}

struct ClosurePassCtx<'a> {
    bindings: &'a BindingPassOutput,
    closures: Vec<ClosureInfo>,
    scope_stack: Vec<ScopeFrame>,
    function_stack: Vec<Option<BindingId>>,
    closure_stack: Vec<ActiveClosure>,
}

#[derive(Debug, Clone)]
struct ScopeFrame {
    bindings: HashMap<Path, BindingId>,
}

impl ScopeFrame {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
struct ActiveClosure {
    parent_binding: BindingId,
    closure_expr: NodeId,
    body_expr: Option<NodeId>,
    scope_index: usize,
    captures: HashSet<BindingId>,
}

impl ActiveClosure {
    fn new(
        parent_binding: BindingId,
        closure_expr: NodeId,
        body_expr: Option<NodeId>,
        scope_index: usize,
    ) -> Self {
        Self {
            parent_binding,
            closure_expr,
            body_expr,
            scope_index,
            captures: HashSet::new(),
        }
    }
}

impl<'a> ClosurePassCtx<'a> {
    fn new(bindings: &'a BindingPassOutput) -> Self {
        Self {
            bindings,
            closures: Vec::new(),
            scope_stack: vec![ScopeFrame::new()],
            function_stack: Vec::new(),
            closure_stack: Vec::new(),
        }
    }

    fn visit_item(&mut self, item: WalkItem<'_>) {
        match item {
            WalkItem::EnterScope(kind) => self.enter_scope(kind),
            WalkItem::ExitScope(kind) => self.exit_scope(kind),
            WalkItem::Decl(decl) => self.visit_decl(decl),
            WalkItem::Expr(expr) => self.visit_expr(expr),
            WalkItem::Pattern(pattern) => self.register_binding_for_node(pattern.id),
            _ => {}
        }
    }

    fn enter_scope(&mut self, kind: WalkScopeKind) {
        self.scope_stack.push(ScopeFrame::new());
        if matches!(kind, WalkScopeKind::Function) {
            self.function_stack.push(None);
        }
    }

    fn exit_scope(&mut self, kind: WalkScopeKind) {
        match kind {
            WalkScopeKind::Closure => {
                if let Some(active) = self.closure_stack.pop() {
                    let mut captures: Vec<BindingId> = active.captures.into_iter().collect();
                    captures.sort_unstable_by_key(|id| id.0);
                    self.closures.push(ClosureInfo {
                        parent_binding: active.parent_binding,
                        captures,
                        body_expr: active.body_expr,
                        closure_expr: active.closure_expr,
                    });
                }
            }
            WalkScopeKind::Function => {
                self.function_stack.pop();
            }
            WalkScopeKind::Block | WalkScopeKind::Module => {}
        }
        self.scope_stack.pop();
    }

    fn visit_decl(&mut self, decl: &crate::ast::Node<Decl>) {
        if let Some(binding) = self.node_binding(decl.id) {
            self.register_binding(binding);
        }

        match &decl.value {
            Decl::Func(func) => {
                if let Some(binding) = self.node_binding(decl.id) {
                    self.set_current_function_binding(Some(binding));
                }
                self.register_function_params(&func.sig.params);
            }
            Decl::Mutable(_)
            | Decl::Name(_)
            | Decl::Declare(_)
            | Decl::Struct(_)
            | Decl::Trait(_)
            | Decl::TypeAlias(_, _)
            | Decl::Extern(_)
            | Decl::Impl(_)
            | Decl::FnSig(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &crate::ast::Node<Expr>) {
        match &expr.value {
            Expr::Closure(closure) => self.visit_closure(expr, closure),
            Expr::Func(func) => self.register_function_params(&func.sig.params),
            Expr::Name(name) => self.record_usage(&name.path),
            Expr::Path(path) => self.record_usage(path),
            _ => {}
        }
    }

    fn visit_closure(&mut self, expr: &crate::ast::Node<Expr>, closure: &Closure) {
        self.register_closure_params(&closure.args.items);
        if let Some(parent_binding) = self.current_parent_binding() {
            if let Some(scope_index) = self.scope_stack.len().checked_sub(1) {
                let context =
                    ActiveClosure::new(parent_binding, expr.id, Some(closure.body.id), scope_index);
                self.closure_stack.push(context);
            }
        }
    }

    fn register_function_params(&mut self, params: &[crate::ast::Node<FnParam>]) {
        for param in params {
            if let Some(binding) = self.node_binding(param.id) {
                self.register_binding(binding);
            }
        }
    }

    fn register_closure_params(&mut self, params: &[crate::ast::Node<Expr>]) {
        for param in params {
            if let Some(binding) = self.node_binding(param.id) {
                self.register_binding(binding);
            }
        }
    }

    fn register_binding_for_node(&mut self, node_id: NodeId) {
        if let Some(binding) = self.node_binding(node_id) {
            self.register_binding(binding);
        }
    }

    fn node_binding(&self, node_id: NodeId) -> Option<BindingId> {
        match self.bindings.node_bindings.get(&node_id).copied()? {
            NodeBinding::Def(binding) => Some(binding),
            NodeBinding::Use(_) => None,
        }
    }

    fn register_binding(&mut self, binding: BindingId) {
        if let Some(record) = self.bindings.binding_records.get(&binding) {
            if let Some(path) = record.path.clone() {
                if let Some(scope) = self.scope_stack.last_mut() {
                    scope.bindings.insert(path, binding);
                }
            }
        }
    }

    fn record_usage(&mut self, path: &Path) {
        let mut defining_scope_index = None;
        let mut binding = None;
        for (idx, scope) in self.scope_stack.iter().enumerate().rev() {
            if let Some(candidate) = scope.bindings.get(path) {
                binding = Some(*candidate);
                defining_scope_index = Some(idx);
                break;
            }
        }
        if let (Some(binding), Some(scope_idx)) = (binding, defining_scope_index) {
            if let Some(active) = self.closure_stack.last_mut() {
                if scope_idx < active.scope_index {
                    active.captures.insert(binding);
                }
            }
        }
    }

    fn set_current_function_binding(&mut self, binding: Option<BindingId>) {
        if let Some(entry) = self.function_stack.last_mut() {
            *entry = binding;
        }
    }

    fn current_parent_binding(&self) -> Option<BindingId> {
        self.function_stack.iter().rev().find_map(|b| *b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Assign, Block, Closure as AstClosure, Expr, Func, Literal, Name, Node,
        Pattern as AstPattern, Sequence,
    };
    use crate::passes::binding;
    use crate::sourcemap::SourceMap;
    use ray_shared::pathlib::{FilePath, Path};
    use ray_shared::span::{Source, Span};
    use ray_typing::NodeBinding;
    use ray_typing::env::GlobalEnv;

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

    fn run_binding_and_closure(
        module: &Module<(), Decl>,
        srcmap: &SourceMap,
    ) -> (BindingPassOutput, ClosurePassOutput) {
        let env = GlobalEnv::default();
        let binding_output = binding::run_binding_pass(module, srcmap, &env, BindingPassOutput::empty());
        let closure_output = run_closure_pass(module, srcmap, &binding_output);
        (binding_output, closure_output)
    }

    #[test]
    fn closure_captures_outer_local() {
        let local_pattern = Node::new(AstPattern::Name(Name::new("outer")));
        let rhs_expr = Node::new(Expr::Literal(Literal::Bool(true)));
        let assign = Assign {
            lhs: local_pattern.clone(),
            rhs: Box::new(rhs_expr.clone()),
            is_mut: false,
            mut_span: None,
            op: crate::ast::InfixOp::Assign,
            op_span: Span::new(),
        };
        let assign_expr = Node::new(Expr::Assign(assign));
        let closure_body = Node::new(Expr::Name(Name::new("outer")));
        let closure = AstClosure {
            args: Sequence::new(vec![]),
            body: Box::new(closure_body.clone()),
            arrow_span: None,
            curly_spans: None,
        };
        let closure_expr = Node::new(Expr::Closure(closure));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![assign_expr.clone(), closure_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::f")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &local_pattern);
        seed_src(&mut srcmap, &assign_expr);
        seed_src(&mut srcmap, &rhs_expr);
        seed_src(&mut srcmap, &closure_expr);
        seed_src(&mut srcmap, &closure_body);

        let (binding_output, closure_output) = run_binding_and_closure(&module, &srcmap);
        assert_eq!(closure_output.closures.len(), 1);
        let info = &closure_output.closures[0];
        let func_binding = match binding_output.node_bindings.get(&decl.id) {
            Some(NodeBinding::Def(binding)) => *binding,
            Some(NodeBinding::Use(_)) => panic!("expected def binding for function"),
            None => panic!("function binding missing"),
        };
        assert_eq!(info.parent_binding, func_binding);
        let local_binding = match binding_output.node_bindings.get(&local_pattern.id) {
            Some(NodeBinding::Def(binding)) => *binding,
            Some(NodeBinding::Use(_)) => panic!("expected def binding for local"),
            None => panic!("local binding missing"),
        };
        assert_eq!(info.captures, vec![local_binding]);
        assert_eq!(info.body_expr, Some(closure_body.id));
        assert_eq!(info.closure_expr, closure_expr.id);
    }

    #[test]
    fn closure_without_captures_reports_empty() {
        let closure_body = Node::new(Expr::Literal(Literal::Bool(true)));
        let closure = AstClosure {
            args: Sequence::new(vec![]),
            body: Box::new(closure_body.clone()),
            arrow_span: None,
            curly_spans: None,
        };
        let closure_expr = Node::new(Expr::Closure(closure));
        let func_body = Node::new(Expr::Block(Block {
            stmts: vec![closure_expr.clone()],
        }));
        let func = Func::new(Node::new(Path::from("pkg::g")), vec![], func_body);
        let decl = Node::new(Decl::Func(func));

        let module = test_module(vec![decl.clone()]);
        let mut srcmap = SourceMap::new();
        seed_src(&mut srcmap, &decl);
        seed_src(&mut srcmap, &closure_expr);
        seed_src(&mut srcmap, &closure_body);

        let (_binding_output, closure_output) = run_binding_and_closure(&module, &srcmap);
        assert_eq!(closure_output.closures.len(), 1);
        assert!(closure_output.closures[0].captures.is_empty());
    }
}
