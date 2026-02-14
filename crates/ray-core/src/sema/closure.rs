use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use ray_shared::{
    def::DefId, local_binding::LocalBindingId, node_id::NodeId, resolution::Resolution,
};
use serde::{Deserialize, Serialize};

use crate::ast::{Closure, Decl, Expr, FnParam, Node, WalkItem, WalkScopeKind, walk_decl};

/// Information about a single closure expression (new API).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClosureInfo {
    pub parent_def: DefId,
    pub captures: Vec<LocalBindingId>,
    pub body_expr: Option<NodeId>,
    pub closure_expr: NodeId,
}

/// Analyze closures within a single definition.
///
/// This is the new per-definition API that will be used by the query system.
pub fn closures_in_def(
    def_id: DefId,
    def_ast: &Node<Decl>,
    resolutions: &HashMap<NodeId, Resolution>,
) -> Vec<ClosureInfo> {
    let lookup = ResolutionLookup {
        current_def: def_id,
        resolutions,
    };
    let mut ctx = ClosureCtx::new(lookup);
    for item in walk_decl(def_ast) {
        ctx.visit_item(item);
    }
    ctx.closures
        .into_iter()
        .map(|c| ClosureInfo {
            parent_def: def_id,
            captures: c.captures,
            body_expr: c.body_expr,
            closure_expr: c.closure_expr,
        })
        .collect()
}

// =============================================================================
// Generic implementation
// =============================================================================

/// Trait for looking up binding information from different sources.
trait BindingLookup {
    type BindingId: Clone + Eq + Hash;

    /// Look up a binding definition for a node (e.g., parameter, let-binding).
    fn binding_for_def(&self, node_id: NodeId) -> Option<Self::BindingId>;

    /// Look up a binding usage for a node (e.g., name reference).
    fn binding_for_use(&self, node_id: NodeId) -> Option<Self::BindingId>;

    /// Get the parent binding (enclosing function) for a declaration node.
    fn parent_binding(&self, node_id: NodeId) -> Option<Self::BindingId>;

    /// Get a sortable key for consistent ordering of captures.
    fn sort_key(id: &Self::BindingId) -> u64;
}

/// Lookup using the new resolution table.
struct ResolutionLookup<'a> {
    current_def: DefId,
    resolutions: &'a HashMap<NodeId, Resolution>,
}

impl<'a> BindingLookup for ResolutionLookup<'a> {
    type BindingId = LocalBindingId;

    fn binding_for_def(&self, node_id: NodeId) -> Option<Self::BindingId> {
        match self.resolutions.get(&node_id)? {
            Resolution::Local(id) if id.owner == self.current_def => Some(*id),
            _ => None,
        }
    }

    fn binding_for_use(&self, node_id: NodeId) -> Option<Self::BindingId> {
        match self.resolutions.get(&node_id)? {
            Resolution::Local(id) if id.owner == self.current_def => Some(*id),
            _ => None,
        }
    }

    fn parent_binding(&self, _node_id: NodeId) -> Option<Self::BindingId> {
        // For the new system, the parent is always the current_def (passed to closures_in_def)
        // We return a dummy LocalBindingId since the caller uses current_def directly
        Some(LocalBindingId::new(self.current_def, 0))
    }

    fn sort_key(id: &Self::BindingId) -> u64 {
        // Combine file, owner index, and local index for sorting
        ((id.owner.file.0 as u64) << 32) | ((id.owner.index as u64) << 16) | (id.index as u64)
    }
}

/// Generic closure info collected during analysis.
struct GenericClosureInfo<B> {
    captures: Vec<B>,
    body_expr: Option<NodeId>,
    closure_expr: NodeId,
}

/// Generic context for closure analysis.
struct ClosureCtx<L: BindingLookup> {
    lookup: L,
    closures: Vec<GenericClosureInfo<L::BindingId>>,
    scope_stack: Vec<GenericScopeFrame<L::BindingId>>,
    function_stack: Vec<Option<L::BindingId>>,
    closure_stack: Vec<GenericActiveClosure<L::BindingId>>,
}

struct GenericScopeFrame<B> {
    bindings: HashMap<B, usize>,
}

impl<B> GenericScopeFrame<B> {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }
}

struct GenericActiveClosure<B> {
    closure_expr: NodeId,
    body_expr: Option<NodeId>,
    scope_index: usize,
    captures: HashSet<B>,
}

impl<L: BindingLookup> ClosureCtx<L> {
    fn new(lookup: L) -> Self {
        Self {
            lookup,
            closures: Vec::new(),
            scope_stack: vec![GenericScopeFrame::new()],
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
        self.scope_stack.push(GenericScopeFrame::new());
        if matches!(kind, WalkScopeKind::Function) {
            self.function_stack.push(None);
        }
    }

    fn exit_scope(&mut self, kind: WalkScopeKind) {
        match kind {
            WalkScopeKind::Closure => {
                if let Some(active) = self.closure_stack.pop() {
                    let mut captures: Vec<L::BindingId> = active.captures.into_iter().collect();
                    captures.sort_unstable_by_key(|id| L::sort_key(id));
                    self.closures.push(GenericClosureInfo {
                        captures,
                        body_expr: active.body_expr,
                        closure_expr: active.closure_expr,
                    });
                }
            }
            WalkScopeKind::Function => {
                self.function_stack.pop();
            }
            WalkScopeKind::Block
            | WalkScopeKind::Module
            | WalkScopeKind::FileMain
            | WalkScopeKind::Impl
            | WalkScopeKind::Trait => {}
        }
        self.scope_stack.pop();
    }

    fn visit_decl(&mut self, decl: &Node<Decl>) {
        if let Some(binding) = self.lookup.binding_for_def(decl.id) {
            self.register_binding(binding.clone());
        }

        if let Decl::Func(func) = &decl.value {
            if let Some(binding) = self.lookup.parent_binding(decl.id) {
                self.set_current_function_binding(Some(binding));
            }
            self.register_function_params(&func.sig.params);
        }
    }

    fn visit_expr(&mut self, expr: &Node<Expr>) {
        match &expr.value {
            Expr::Closure(closure) => self.visit_closure(expr, closure),
            Expr::Func(func) => self.register_function_params(&func.sig.params),
            Expr::Name(_) | Expr::Path(_) => self.record_usage(expr.id),
            _ => {}
        }
    }

    fn visit_closure(&mut self, expr: &Node<Expr>, closure: &Closure) {
        self.register_closure_params(&closure.args.items);
        let scope_index = self.scope_stack.len().saturating_sub(1);
        self.closure_stack.push(GenericActiveClosure {
            closure_expr: expr.id,
            body_expr: Some(closure.body.id),
            scope_index,
            captures: HashSet::new(),
        });
    }

    fn register_function_params(&mut self, params: &[Node<FnParam>]) {
        for param in params {
            self.register_binding_for_node(param.id);
        }
    }

    fn register_closure_params(&mut self, params: &[Node<Expr>]) {
        for param in params {
            self.register_binding_for_node(param.id);
        }
    }

    fn register_binding_for_node(&mut self, node_id: NodeId) {
        if let Some(binding) = self.lookup.binding_for_def(node_id) {
            self.register_binding(binding);
        }
    }

    fn register_binding(&mut self, binding: L::BindingId) {
        let scope_index = self.scope_stack.len().saturating_sub(1);
        if let Some(scope) = self.scope_stack.last_mut() {
            scope.bindings.insert(binding, scope_index);
        }
    }

    fn record_usage(&mut self, node_id: NodeId) {
        let binding = match self.lookup.binding_for_use(node_id) {
            Some(b) => b,
            None => return,
        };

        // Find what scope this binding was defined in
        let defining_scope_index = self
            .scope_stack
            .iter()
            .enumerate()
            .rev()
            .find_map(|(idx, scope)| scope.bindings.get(&binding).map(|_| idx));

        // If defined outside the closure's scope, it's a capture
        if let Some(scope_idx) = defining_scope_index {
            if let Some(active) = self.closure_stack.last_mut() {
                if scope_idx < active.scope_index {
                    active.captures.insert(binding);
                }
            }
        }
    }

    fn set_current_function_binding(&mut self, binding: Option<L::BindingId>) {
        if let Some(entry) = self.function_stack.last_mut() {
            *entry = binding;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        ast::{
            Assign, Block, Closure as AstClosure, Decl, Expr, Func, InfixOp, Literal, Name, Node,
            Pattern as AstPattern, Sequence,
        },
        sema::closure::closures_in_def,
    };
    use ray_shared::{
        def::DefId, file_id::FileId, local_binding::LocalBindingId, node_id::NodeId, pathlib::Path,
        resolution::Resolution, span::Span,
    };

    #[test]
    fn closures_in_def_captures_outer_local() {
        let def_id = DefId::new(FileId(0), 1);
        let _guard = NodeId::enter_def(def_id);

        // Build AST: fn f() { outer = true; || outer }
        let local_pattern = Node::new(AstPattern::Name(Name::new("outer")));
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

        // Build resolution table: local_pattern defines a local, closure_body uses it
        let local_id = LocalBindingId::new(def_id, 1);
        let mut resolutions = HashMap::new();
        resolutions.insert(local_pattern.id, Resolution::Local(local_id));
        resolutions.insert(closure_body.id, Resolution::Local(local_id));

        let closures = closures_in_def(def_id, &decl, &resolutions);
        assert_eq!(closures.len(), 1);
        let info = &closures[0];
        assert_eq!(info.parent_def, def_id);
        assert_eq!(info.captures, vec![local_id]);
        assert_eq!(info.body_expr, Some(closure_body.id));
        assert_eq!(info.closure_expr, closure_expr.id);
    }

    #[test]
    fn closures_in_def_no_captures() {
        let def_id = DefId::new(FileId(0), 1);
        let _guard = NodeId::enter_def(def_id);

        // Build AST: fn f() { || true }
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

        // No resolutions needed - closure body is a literal
        let resolutions = HashMap::new();

        let closures = closures_in_def(def_id, &decl, &resolutions);
        assert_eq!(closures.len(), 1);
        assert!(closures[0].captures.is_empty());
    }
}
