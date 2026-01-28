// Per-module and per-binding-group typing context.
// This is a stripped-down, spec-aligned analogue of the existing TyCtx.

use std::collections::{HashMap, HashSet};

use ray_shared::{
    binding_target::BindingTarget,
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ItemPath, Path},
    ty::{SKOLEM_PREFIX, SchemaVarAllocator, Ty, TyVar},
};

use crate::{
    constraint_tree::SkolemizedAnnotation,
    constraints::{ClassPredicate, Constraint, Predicate},
    env::TypecheckEnv,
    info::TypeSystemInfo,
    types::{Subst, Substitutable, TyScheme},
};

/// Minimal expression and pattern kinds used for v2 constraint generation.
///
/// This is intentionally tiny and decoupled from the real frontend AST; the
/// frontend will translate its own nodes into this shape for the typechecker.
#[derive(Clone, Debug)]
pub enum Pattern {
    /// Wildcard `_`.
    Wild,
    /// Plain binding pattern `x`.
    Binding(LocalBindingId),
    /// `some(x)` pattern for nilable types (used by pattern-if and
    /// pattern-while, see the spec's "Pattern-if" and "Pattern-while").
    Some(LocalBindingId),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    /// A reference to a local binding (parameter, let-binding, etc.).
    LocalRef(LocalBindingId),
    /// A reference to a top-level definition.
    DefRef(DefId),
    /// A scoped access `T::member`.
    ///
    /// Note: any type arguments in `T[...]::member` belong to the left-hand
    /// side type `T[...]`, not to the member itself.
    ScopedAccess {
        def_id: DefId,
        member_name: String,
        lhs_ty: Ty,
    },
    /// An integer literal without an explicit size suffix; its concrete
    /// type is determined by the `Int` class constraints and defaulting.
    LiteralInt,
    /// An integer literal with an explicit size suffix (e.g. `1u32`). Its
    /// type is expected to be fixed by surrounding annotations and we do
    /// not introduce an `Int` class predicate for it.
    LiteralIntSized(Ty),
    /// A floating-point literal without an explicit size suffix; its
    /// concrete type is determined by the `Float` class constraints and
    /// defaulting.
    LiteralFloat,
    /// A floating-point literal with an explicit size suffix (e.g. `1.0f64`).
    /// Its type is expected to be fixed by surrounding annotations, so we
    /// do not introduce a `Float` class predicate for it.
    LiteralFloatSized,
    /// A boolean literal `true` or `false`.
    LiteralBool(bool),
    /// String literal `"..."`.
    LiteralString,
    /// Byte-string literal `b"..."`.
    LiteralByteString,
    /// Single byte literal `b'x'`.
    LiteralByte,
    /// Character literal `'x'`.
    LiteralChar,
    /// Unicode escape sequence literal.
    LiteralUnicodeEsc,
    /// Meta-type expression `type[T]` used at runtime by intrinsics like `sizeof`.
    ///
    /// This is an expression whose value is a "type object" (represented in the
    /// type system as `type[T]`), not a normal runtime value of type `T`.
    Type { ty: Ty },
    /// Struct construction `A { x: e1, y: e2 }`.
    StructLiteral {
        path: ItemPath,
        fields: Vec<(String, NodeId)>,
    },
    /// Anonymous function expression `fn(p1, ..., pn) { body }`.
    /// Parameters are represented as bindings in `params`, and `body` is
    /// the expression identifier for the function body.
    Closure {
        params: Vec<LocalBindingId>,
        body: NodeId,
    },
    /// `some(e)` for nilable literals (Section "Nilable literals").
    Some { expr: NodeId },
    /// Bare `nil` literal (Section "Nilable literals").
    Nil,
    /// Top-level or named function binding. Unlike closures, these correspond
    /// to declared functions and always carry binding identifiers for their
    /// parameters.
    Function {
        params: Vec<LocalBindingId>,
        body: NodeId,
    },
    /// If expression `if cond { then_expr } else { else_expr }`.
    If {
        cond: NodeId,
        then_branch: NodeId,
        else_branch: Option<NodeId>,
    },
    /// Pattern-if `if pat = e { then } else { else }`, modeled after the
    /// "Pattern-if" rule in docs/type-system.md.
    IfPattern {
        scrutinee: NodeId,
        pattern: Pattern,
        then_branch: NodeId,
        else_branch: Option<NodeId>,
    },
    /// While expression `while cond { body }`, following the rule in
    /// docs/type-system.md "While expressions".
    While { cond: NodeId, body: NodeId },
    /// Pattern-while `while pat = e { body }`, following the
    /// "Pattern-while" rule in the spec.
    WhilePattern {
        scrutinee: NodeId,
        pattern: Pattern,
        body: NodeId,
    },
    /// `loop { body }`, as in the "Loop and break" rule.
    Loop { body: NodeId },
    /// `break e` or bare `break` in a loop.
    Break { expr: Option<NodeId> },
    /// `continue` within a loop.
    Continue,
    /// `return e` from within a function (see "Return expressions").
    Return { expr: Option<NodeId> },
    /// Heap allocation / boxing `box e`, treated as producing a pointer
    /// type `*T` when `e : T` (see docs/type-system.md Section 1.1
    /// "Pointer types").
    Boxed { expr: NodeId },
    /// Dereference `*e`, which in the core type system has type `T` when
    /// `e : *T` (Section 1.1 "Pointer types").
    Deref { expr: NodeId },
    /// Explicit reference `ref e`, which has type `*T` when `e : T`.
    Ref { expr: NodeId },
    /// Tuple expression `(e0, e1, ..., en)`.
    Tuple { elems: Vec<NodeId> },
    /// `for pat in e { body }` using the `Iter[Recv, Elem]` trait, as
    /// described in the "For loops" rule.
    For {
        pattern: Pattern,
        iter_expr: NodeId,
        body: NodeId,
    },
    /// Field access `recv.field`.
    FieldAccess { recv: NodeId, field: String },
    /// Structured sequencing/block expression with ordered child expressions.
    /// Its type is the type of the final item.
    Sequence { items: Vec<NodeId> },
    /// A function call expression: `callee(args...)`.
    Call { callee: NodeId, args: Vec<NodeId> },
    /// List literal `[e0, e1, ..., en]`. The element type is inferred
    /// from the items and related to the list's element type via the
    /// `Index` and `Iter` traits (docs/type-system.md Section A.3).
    List { items: Vec<NodeId> },
    /// Dict literal `{ k0: v0, k1: v1, ..., kn: vn }`.
    Dict { entries: Vec<(NodeId, NodeId)> },
    /// Set literal `{ e0, e1, ..., en, }` (trailing comma required for singleton).
    Set { items: Vec<NodeId> },
    /// Range expression `start .. end` or `start ..= end`, which has
    /// nominal type `range[T]` for some element type `T` shared by the
    /// endpoints.
    Range {
        start: NodeId,
        end: NodeId,
        inclusive: bool,
    },
    /// Binary operator application `e1 op e2`, typed via an operator
    /// trait `OpTrait[Left, Right, Result]` (docs/type-system.md,
    /// "Operators"). `trait_name` is the name of that trait (e.g. "Add").
    BinaryOp {
        trait_fqn: ItemPath,
        method_fqn: ItemPath,
        lhs: NodeId,
        rhs: NodeId,
        operator: NodeId,
    },
    /// Operator token `op` for an operator expression. This node represents the
    /// function that implements the operator, so its type is
    /// `(Targs...) -> Tresult`.
    OpFunc {
        trait_name: String,
        args: Vec<NodeId>,
        result: NodeId,
    },
    /// Unary operator application `op e`, typed via a unary operator
    /// trait `UnaryOpTrait[Arg, Result]` (e.g. "Neg").
    UnaryOp {
        trait_fqn: ItemPath,
        method_fqn: ItemPath,
        operator: NodeId,
        expr: NodeId,
    },
    /// Cast expression `e as Tcast` (docs/type-system.md A.9).
    ///
    /// This carries the target type so constraint generation can relate the
    /// cast expression's type to `Tcast`.
    Cast { expr: NodeId, ty: Ty },
    /// Indexing operation `container[index]`, which generates an
    /// `Index[ContainerTy, ElemTy, IndexTy]` predicate (see the
    /// `Index` trait in docs/type-system.md Section A.3).
    Index { container: NodeId, index: NodeId },
    /// Heap allocation `new(T, count?)`. For now we only track the optional
    /// count expression; the target type `T` comes from the frontend's
    /// annotation and is not yet threaded into this IR.
    New { count: Option<NodeId> },
    /// Placeholder for a missing expression in the parsed AST. This is
    /// treated as an unconstrained fresh type so that type checking can
    /// continue on partially-invalid programs.
    Missing,
    /// Assignment expression `lhs = rhs` (docs/type-system.md A.8).
    /// The left-hand side is represented in a simplified, l-value–oriented
    /// form; for now we support only simple name bindings, with richer
    /// patterns and mutation targets to be added incrementally.
    Assign {
        lhs_pattern: NodeId,
        lhs: AssignLhs,
        rhs: NodeId,
    },
    /// Transparent wrapper node (e.g. parentheses, labeled expressions)
    /// that should behave like its inner expression but retain its own id.
    Wrapper { expr: NodeId },
}

/// Pattern subtree for binding/destructuring assignment on the left-hand
/// side of `lhs = rhs`, corresponding to the pattern typing judgment
/// in docs/type-system.md A.7.
#[derive(Clone, Debug)]
pub enum LhsPattern {
    /// Simple variable pattern `x`, which binds or reuses a single name.
    Binding(LocalBindingId),
    /// Tuple / sequence pattern `(p1, ..., pn)` or `p1, ..., pn`, matching
    /// a tuple scrutinee `tuple[T1, ..., Tn]` and recursively typing the
    /// subpatterns against the component types.
    Tuple(Vec<LhsPattern>),
    /// Struct pattern `A { x = p1, y = p2, ... }` for a nominal record
    /// type `A`, where each field pattern is typed against the declared
    /// field type using `HasField` constraints (see docs/type-system.md
    /// Sections 4.5 and A.8 for struct patterns).
    Struct {
        struct_name: String,
        fields: Vec<(String, LhsPattern)>,
    },
}

/// Simplified shape of assignment left-hand sides for constraint generation,
/// corresponding to the cases in docs/type-system.md A.8. This separates
/// binding/destructuring patterns from mutation-specific forms.
#[derive(Clone, Debug)]
pub enum AssignLhs {
    /// Binding/destructuring pattern `lhs`, interpreted via the general
    /// pattern typing judgment Γ ⊢ lhs : Trhs ⇝ (Δ, Cp) from A.7/A.8.
    Pattern(LhsPattern),
    /// Deref assignment `*p = rhs` where `p` is a simple variable.
    /// This corresponds to the deref-assignment rule in Section A.8.
    Deref(LocalBindingId),
    /// Field assignment `recv.field = rhs` where `recv` is a simple variable.
    /// This corresponds to the field-assignment rule in Section A.8.
    Field { recv: LocalBindingId, field: String },
    /// Index assignment `container[index] = rhs`, which uses the
    /// `Index[Container, Elem, Index]` trait as described in
    /// docs/type-system.md A.8.
    ///
    /// The `container` is a NodeId representing the container expression,
    /// which may be a simple local reference or a nested index expression
    /// (e.g., `m[0]` in `m[0][1] = v`).
    Index {
        container: NodeId,
        index: NodeId,
    },
    /// Error placeholder produced from a `Missing` pattern on the left-hand
    /// side. This allows type checking to continue for the right-hand side
    /// and surrounding expression without introducing bindings or additional
    /// equalities beyond `expr_ty == unit`.
    ErrorPlaceholder,
    // Future extensions (left as TODO in lowering/constraints):
    // - Index assignments `container[index] = rhs`
    // - Struct patterns such as `A { x, y } = rhs` inside LhsPattern.
}

// For now this holds just enough structure to make the intended shape of the
// context obvious, without committing to any frontend details.
pub struct SolverContext<'a> {
    /// Inferred or expected mono types for expressions.
    pub expr_types: HashMap<NodeId, Ty>,

    /// Schemes associated with bindings (both local and top-level definitions).
    pub binding_schemes: HashMap<BindingTarget, TyScheme>,

    /// Bindings that had an explicit (frontend-provided) annotation.
    ///
    /// Note: monomorphic annotations have empty `TyScheme.vars` and
    /// `TyScheme.qualifiers`, so we track "explicitness" separately to avoid
    /// incorrectly treating them as inferred and generalizing them.
    pub explicitly_annotated: HashSet<BindingTarget>,

    /// Skolemized schemes associated with bindings.
    pub skolemized_schemes: HashMap<BindingTarget, SkolemizedAnnotation>,

    /// Meta variables that were intentionally generalized into a `forall`
    /// during `generalize_group`. These should not be treated as "unsolved"
    /// leaks when checking expression types post-solve.
    pub generalized_metas: HashSet<TyVar>,

    /// Failed class predicate attempts (e.g. impl head matched, but predicates failed).
    pub predicate_failures: Vec<PredicateFailure>,

    /// Counter used to generate fresh meta type variables for expressions.
    next_meta_id: u32,

    /// Reusable fresh metas variables.
    reusable_metas: Vec<TyVar>,

    /// Stack of function result types `Tret` for the current function
    /// context, used when generating constraints for `return` expressions
    /// (see docs/type-system.md "Return expressions").
    fn_ret_stack: Vec<Ty>,

    /// Stack of loop result types `?L` for the current loop context, used
    /// when generating constraints for `loop`/`break` (see
    /// docs/type-system.md "Loop and break").
    loop_result_stack: Vec<Ty>,

    /// Unique id counter for skolem variables introduced while checking
    /// annotated bindings.
    next_skolem_id: u32,

    /// Per-binding list of skolems currently in scope.
    binding_skolems: HashMap<BindingTarget, Vec<TyVar>>,

    /// Metadata for each skolem variable.
    skolem_metadata: HashMap<TyVar, SkolemMetadata>,

    /// Predicates required by annotated bindings (after skolemization).
    binding_required_preds: HashMap<BindingTarget, Vec<Predicate>>,

    /// Shared allocator for schema variables.
    schema_allocator: &'a mut SchemaVarAllocator,

    /// External typecheck environment
    env: &'a dyn TypecheckEnv,

    /// Optional callback for looking up external schemes (e.g., from previously-checked
    /// binding groups in incremental compilation).
    external_schemes: Option<Box<dyn Fn(DefId) -> Option<TyScheme> + 'a>>,
}

pub trait MetaAllocator {
    fn fresh_meta(&mut self) -> Ty;
    fn reuse_metas(&mut self, metas: Vec<TyVar>);
}

impl<'a> MetaAllocator for SolverContext<'a> {
    fn fresh_meta(&mut self) -> Ty {
        SolverContext::fresh_meta(self)
    }

    fn reuse_metas(&mut self, metas: Vec<TyVar>) {
        SolverContext::reuse_metas(self, metas)
    }
}

impl<'a> SolverContext<'a> {
    pub fn new(schema_allocator: &'a mut SchemaVarAllocator, env: &'a dyn TypecheckEnv) -> Self {
        SolverContext {
            expr_types: HashMap::new(),
            binding_schemes: HashMap::new(),
            explicitly_annotated: HashSet::new(),
            skolemized_schemes: HashMap::new(),
            next_meta_id: 0,
            reusable_metas: vec![],
            fn_ret_stack: vec![],
            loop_result_stack: vec![],
            next_skolem_id: 0,
            binding_skolems: HashMap::new(),
            skolem_metadata: HashMap::new(),
            binding_required_preds: HashMap::new(),
            schema_allocator,
            env,
            generalized_metas: HashSet::new(),
            predicate_failures: Vec::new(),
            external_schemes: None,
        }
    }

    pub fn is_explicitly_annotated(&self, target: impl Into<BindingTarget>) -> bool {
        self.explicitly_annotated.contains(&target.into())
    }

    pub fn record_predicate_failure(
        &mut self,
        wanted: &Constraint,
        instance_failure: InstanceFailure,
    ) {
        if self
            .predicate_failures
            .iter()
            .any(|entry| entry.wanted == *wanted)
        {
            return;
        }
        self.predicate_failures.push(PredicateFailure {
            wanted: wanted.clone(),
            instance_failure,
        });
    }

    /// Apply a type substitution to all tracked types and schemes.
    pub fn apply_subst(&mut self, subst: &Subst) {
        for ty in self.expr_types.values_mut() {
            ty.apply_subst(subst);
        }
        for scheme in self.binding_schemes.values_mut() {
            scheme.apply_subst(subst);
        }

        for ty in &mut self.fn_ret_stack {
            ty.apply_subst(subst);
        }
        for ty in &mut self.loop_result_stack {
            ty.apply_subst(subst);
        }

        for preds in self.binding_required_preds.values_mut() {
            for pred in preds {
                pred.apply_subst(subst);
            }
        }
    }

    /// Allocate a fresh meta type variable for use in constraints, e.g. the
    /// type of an expression before solving.
    pub fn fresh_meta(&mut self) -> Ty {
        if let Some(meta) = self.reusable_metas.pop() {
            return Ty::Var(meta);
        }

        let id = self.next_meta_id;
        self.next_meta_id += 1;

        let mut path = Path::new();
        path.append_mut(format!("?t{}", id));
        Ty::Var(TyVar::new(path))
    }

    /// Add a fresh meta variable to the reuse stack
    pub fn reuse_metas(&mut self, metas: impl IntoIterator<Item = TyVar>) {
        self.reusable_metas.extend(metas);
    }

    /// Lookup the type of an expression, allocating a fresh meta if it has
    /// not been seen before. This helper centralizes the common "if ty
    /// exists else fresh" pattern used throughout constraint generation.
    pub fn expr_ty_or_fresh(&mut self, expr: NodeId) -> Ty {
        if let Some(ty) = self.expr_types.get(&expr) {
            ty.clone()
        } else {
            let ty = self.fresh_meta();
            self.expr_types.insert(expr, ty.clone());
            ty
        }
    }

    /// Lookup the type of a binding, allocating a fresh meta and inserting a
    /// mono scheme if it has not been seen before. This mirrors the common
    /// "if scheme exists else fresh" pattern used when relating bindings to
    /// their body expressions.
    pub fn binding_ty_or_fresh(&mut self, target: impl Into<BindingTarget>) -> Ty {
        let target = target.into();
        if let Some(scheme) = self.binding_schemes.get(&target) {
            scheme.ty.clone()
        } else {
            let ty = self.fresh_meta();
            self.binding_schemes
                .insert(target, TyScheme::from_mono(ty.clone()));
            ty
        }
    }

    /// Push a function result type `Tret` for the current function context.
    pub fn push_fn_ret(&mut self, ty: Ty) {
        self.fn_ret_stack.push(ty);
    }

    /// Pop the current function result type, if any.
    pub fn pop_fn_ret(&mut self) {
        self.fn_ret_stack.pop();
    }

    /// Get the current function result type, if any.
    pub fn current_fn_ret(&self) -> Option<Ty> {
        self.fn_ret_stack.last().cloned()
    }

    /// Push a loop result type `?L` for the current loop context.
    pub fn push_loop_result(&mut self, ty: Ty) {
        self.loop_result_stack.push(ty);
    }

    /// Pop the current loop result type, if any.
    pub fn pop_loop_result(&mut self) {
        self.loop_result_stack.pop();
    }

    /// Get the current loop result type, if any.
    pub fn current_loop_result(&self) -> Option<Ty> {
        self.loop_result_stack.last().cloned()
    }

    /// Allocate a fresh skolem variable for a binding annotation and
    /// record metadata for later diagnostics.
    pub fn fresh_skolem_var(
        &mut self,
        target: impl Into<BindingTarget>,
        schema_var: TyVar,
        info: &TypeSystemInfo,
    ) -> TyVar {
        let target = target.into();
        let id = self.next_skolem_id;
        self.next_skolem_id += 1;
        let name = format!("{}{}", SKOLEM_PREFIX, id);
        let var = TyVar::new(name);
        self.binding_skolems
            .entry(target)
            .or_default()
            .push(var.clone());
        self.skolem_metadata.insert(
            var.clone(),
            SkolemMetadata {
                target,
                schema_var,
                info: info.clone(),
            },
        );
        var
    }

    /// Lookup metadata for a recorded skolem variable.
    pub fn skolem_info(&self, var: &TyVar) -> Option<&SkolemMetadata> {
        self.skolem_metadata.get(var)
    }

    /// Build a substitution that maps the skolems introduced for a binding
    /// back to the original schema variables from its annotation scheme.
    pub fn skolem_to_schema_subst(&self, target: impl Into<BindingTarget>) -> Subst {
        let target = target.into();
        let mut subst = Subst::new();
        if let Some(vars) = self.binding_skolems.get(&target) {
            for skolem in vars {
                if let Some(meta) = self.skolem_metadata.get(skolem) {
                    subst.insert(skolem.clone(), Ty::Var(meta.schema_var.clone()));
                }
            }
        }
        subst
    }

    /// Remove skolem metadata for a binding once it is no longer needed.
    pub fn clear_skolems(&mut self, target: impl Into<BindingTarget>) {
        let target = target.into();
        if let Some(vars) = self.binding_skolems.remove(&target) {
            for var in vars {
                self.skolem_metadata.remove(&var);
            }
        }
    }

    /// Record that a binding's annotation required a predicate.
    pub fn record_required_predicate(
        &mut self,
        target: impl Into<BindingTarget>,
        predicate: Predicate,
    ) {
        self.binding_required_preds
            .entry(target.into())
            .or_default()
            .push(predicate);
    }

    /// Access recorded required predicates for a binding.
    pub fn required_predicates(&self, target: impl Into<BindingTarget>) -> Option<&[Predicate]> {
        self.binding_required_preds
            .get(&target.into())
            .map(|v| v.as_slice())
    }

    pub fn schema_allocator_mut(&mut self) -> &mut SchemaVarAllocator {
        self.schema_allocator
    }

    pub fn alloc_schema_var(&mut self) -> TyVar {
        self.schema_allocator.alloc()
    }

    pub fn env(&self) -> &dyn TypecheckEnv {
        self.env
    }

    /// Set the external schemes callback for looking up schemes from
    /// previously-checked binding groups.
    pub fn set_external_schemes(&mut self, callback: impl Fn(DefId) -> Option<TyScheme> + 'a) {
        self.external_schemes = Some(Box::new(callback));
    }

    /// Lookup a scheme for a top-level definition.
    ///
    /// Checks in order:
    /// 1. `binding_schemes` (schemes from the current/previous binding groups)
    /// 2. `external_schemes` callback (for incremental compilation)
    /// 3. `env.external_scheme()` (for externally-defined schemes)
    pub fn lookup_def_scheme(&self, def_id: DefId) -> Option<TyScheme> {
        if let Some(scheme) = self.binding_schemes.get(&def_id.into()) {
            return Some(scheme.clone());
        }
        if let Some(callback) = &self.external_schemes {
            if let Some(scheme) = callback(def_id) {
                return Some(scheme);
            }
        }
        // Fall back to the environment (e.g., for extern declarations)
        self.env.external_scheme(def_id)
    }
}

#[derive(Clone, Debug)]
pub struct PredicateFailure {
    pub wanted: Constraint,
    pub instance_failure: InstanceFailure,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstanceFailureStatus {
    NoMatchingImpl,
    HeadMatchFailed,
    Deferred,
}

#[derive(Clone, Debug)]
pub struct InstanceFailure {
    pub status: InstanceFailureStatus,
    pub failures: Vec<ImplFailure>,
}

#[derive(Clone, Debug)]
pub struct ImplFailure {
    pub impl_head: ClassPredicate,
    pub unsatisfied: Vec<Constraint>,
}

/// Metadata associated with skolem variables introduced for annotated
/// bindings. This mirrors the diagnostics produced when missing predicates
/// or skolem escapes are reported.
#[derive(Clone, Debug)]
pub struct SkolemMetadata {
    pub target: BindingTarget,
    pub schema_var: TyVar,
    pub info: TypeSystemInfo,
}
