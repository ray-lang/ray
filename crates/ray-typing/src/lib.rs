pub mod binding_groups;
pub mod bundles;
pub mod constraint_tree;
pub mod constraints;
pub mod context;
pub mod defaulting;
pub mod env;
pub mod generalize;
pub mod goal_solver;
pub mod impl_match;
pub mod info;
pub mod mocks;
pub mod path;
pub mod term_solver;
pub mod tyctx;
pub mod types;
pub mod unify;

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    mem,
};

use ray_shared::{
    binding_target::BindingTarget,
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::Path,
    resolution::DefTarget,
    span::Source,
    ty::{SchemaVarAllocator, Ty, TyVar},
};

use crate::{
    binding_groups::{BindingGraph, BindingGroup, BindingId},
    constraint_tree::{
        ConstraintNode, ConstraintTreeWalkItem, build_constraint_tree_for_group, walk_tree,
    },
    constraints::{Constraint, ConstraintKind, InstantiateTarget, MemberAccessKind, Predicate},
    context::{AssignLhs, ExprKind, InstanceFailureStatus, SolverContext},
    defaulting::{DefaultingLog, DefaultingOutcomeKind, DefaultingResult, apply_defaulting},
    env::TypecheckEnv,
    generalize::generalize_group,
    info::{Info, TypeSystemInfo},
    tyctx::TyCtx,
    types::{MethodResolutionInfo, Subst, Substitutable as _, TyScheme},
};

/// Associates a frontend node with a binding, distinguishing between
/// definition sites (binders) and use sites (references).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeBinding {
    Def(BindingId),
    Use(BindingId),
}

impl NodeBinding {
    pub fn binding(self) -> BindingId {
        match self {
            NodeBinding::Def(b) | NodeBinding::Use(b) => b,
        }
    }
}

/// Describes what a particular binding represents so later phases can
/// interpret its scheme and expression subtree correctly.
#[derive(Clone, Debug)]
pub enum BindingKind {
    /// A function binding with parameters and a result type (`Ty::Func`).
    Function {
        /// Binding identifiers for each parameter, in order.
        params: Vec<LocalBindingId>,
    },
    /// A plain value binding (let-binding, constant, etc.).
    Value,
    /// Placeholder for future pattern/destructuring bindings.
    Pattern,
}

/// Consolidated metadata for a binding introduced by the frontend.
#[derive(Clone, Debug)]
pub struct BindingRecord {
    /// Fully-qualified path for diagnostics and `TyCtx` lookups.
    pub path: Option<Path>,
    /// True if this binding is an external stub injected from a dependency
    /// interface, rather than originating from the current module's AST.
    pub is_extern: bool,
    /// True if this binding represents a mutable slot (`mut x`).
    pub is_mut: bool,
    /// Classification of the binding (function/value/etc.).
    pub kind: BindingKind,
    /// Annotated scheme, if any. When populated this will be skolemized
    /// prior to constraint generation. For unannotated bindings this
    /// starts as `None` until we synthesize a scheme.
    pub scheme: Option<TyScheme>,
    /// Expression representing the body/RHS of the binding.
    pub body_expr: Option<NodeId>,
    /// Source information used for diagnostics.
    pub sources: Vec<Source>,
    /// Optional parent binding; populated for bindings defined inside other bindings.
    pub parent: Option<BindingId>,
}

impl BindingRecord {
    pub fn new(kind: BindingKind) -> Self {
        BindingRecord {
            path: None,
            is_extern: false,
            is_mut: false,
            kind,
            scheme: None,
            body_expr: None,
            sources: vec![],
            parent: None,
        }
    }
}

/// Normalized metadata for AST patterns that participate in typing.
#[derive(Clone, Debug)]
pub struct PatternRecord {
    pub kind: PatternKind,
    pub source: Option<Source>,
}

/// Simplified shapes of patterns recorded during lowering.
#[derive(Clone, Debug)]
pub enum PatternKind {
    /// Simple binding like `x`.
    Binding { binding: LocalBindingId },
    /// Tuple or sequence pattern `(p1, ..., pn)` / `p1, ..., pn`.
    Tuple { elems: Vec<NodeId> },
    /// Field projection `base.field`.
    Field { base: NodeId, field: String },
    /// Index projection `container[index]`.
    Index { container: NodeId, index: NodeId },
    /// Dereference pattern `*x`.
    Deref { binding: LocalBindingId },
    /// `some(x)` pattern for guard patterns (for-loops, if-let).
    /// The binding is the inner pattern's LocalBindingId.
    Some { binding: LocalBindingId },
    /// Placeholder for unsupported or missing patterns so we can still
    /// assign a type to the node.
    Missing,
}

/// Metadata for expressions emitted by the lowering pipeline.
#[derive(Clone, Debug)]
pub struct ExprRecord {
    pub kind: ExprKind,
    pub source: Option<Source>,
}

#[derive(Clone, Debug)]
pub struct TypeCheckInput {
    pub bindings: BindingGraph<DefId>,
    /// Mapping from DefId to the root NodeId of its body expression.
    /// This replaces `BindingRecord.body_expr` - the actual expression
    /// metadata is in `expr_records`.
    pub def_nodes: HashMap<DefId, NodeId>,
    /// Top-level statements for each file's FileMain (DefId with index 0).
    /// These are typechecked but don't have a single "root" expression.
    pub file_main_stmts: HashMap<DefId, Vec<NodeId>>,
    /// Consolidated expression metadata keyed by NodeId, replacing the
    /// expr_kinds/expr_sources split as the new lowering pipeline lands.
    pub expr_records: HashMap<NodeId, ExprRecord>,
    /// Simplified pattern metadata so every AST pattern node can be typed.
    pub pattern_records: HashMap<NodeId, PatternRecord>,
    /// Errors recorded during lowering before the solver runs.
    pub lowering_errors: Vec<TypeError>,
}

impl TypeCheckInput {
    /// Compute binding groups.
    ///
    /// - Walk the bindings and build a dependency graph over
    ///   `DefId`.
    /// - Compute strongly connected components (SCCs) of this graph.
    /// - Return one `BindingGroup` per SCC, in a topologically sorted order
    ///   so groups can only depend on earlier groups.
    pub fn binding_groups(&self) -> Vec<BindingGroup<DefId>> {
        // All definitions in def_nodes are top-level workspace definitions.
        // External definitions (from libraries) are not included in TypeCheckInput.
        let top_level: BTreeSet<DefId> = self.def_nodes.keys().copied().collect();
        self.bindings.compute_binding_groups_over(&top_level)
    }

    /// Return the root expression for a given binding, if any.
    pub fn binding_root_expr(&self, id: DefId) -> Option<NodeId> {
        self.def_nodes.get(&id).copied()
    }

    /// Get the function parameters for a binding, if it's a function.
    /// Returns None for non-function bindings.
    pub fn binding_params(&self, id: DefId) -> Option<&Vec<LocalBindingId>> {
        let root = self.def_nodes.get(&id)?;
        let record = self.expr_records.get(root)?;
        match &record.kind {
            ExprKind::Function { params, .. } => Some(params),
            _ => None,
        }
    }

    /// Check if a binding is a function.
    pub fn is_function_binding(&self, id: DefId) -> bool {
        self.binding_params(id).is_some()
    }

    /// Return the direct child expressions of the given expression.
    ///
    /// This is a placeholder for the real AST shape; in a complete
    /// implementation it would return the IDs of sub-expressions (operands,
    /// block contents, branch bodies, etc.) so constraint generation can walk
    /// the expression tree.
    pub fn expr_children(&self, expr: NodeId) -> Vec<NodeId> {
        let out = match self.expr_records.get(&expr).map(|rec| &rec.kind) {
            Some(ExprKind::Call { callee, args }) => {
                let mut out = Vec::with_capacity(1 + args.len());
                out.push(*callee);
                out.extend(args.iter().copied());
                out
            }
            Some(ExprKind::If {
                cond,
                then_branch,
                else_branch,
            }) => {
                let mut out = vec![*cond, *then_branch];
                if let Some(e) = else_branch {
                    out.push(*e);
                }
                out
            }
            Some(ExprKind::IfPattern {
                scrutinee,
                then_branch,
                else_branch,
                ..
            }) => {
                let mut out = vec![*scrutinee, *then_branch];
                if let Some(e) = else_branch {
                    out.push(*e);
                }
                out
            }
            Some(ExprKind::While { cond, body }) => vec![*cond, *body],
            Some(ExprKind::WhilePattern {
                scrutinee, body, ..
            }) => vec![*scrutinee, *body],
            Some(ExprKind::Loop { body }) => vec![*body],
            Some(ExprKind::Break { expr }) => expr.iter().copied().collect(),
            Some(ExprKind::Continue) => vec![],
            Some(ExprKind::Return { expr }) => {
                if let Some(expr) = expr {
                    vec![*expr]
                } else {
                    vec![]
                }
            }
            Some(ExprKind::For {
                pattern: _,
                iter_expr,
                body,
            }) => {
                vec![*iter_expr, *body]
            }
            Some(ExprKind::FieldAccess { recv, .. }) => vec![*recv],
            Some(ExprKind::Sequence { items }) => items.clone(),
            Some(ExprKind::Closure { params: _, body }) => vec![*body],
            Some(ExprKind::Function { params: _, body }) => vec![*body],
            Some(ExprKind::List { items }) => items.clone(),
            Some(ExprKind::Dict { entries }) => {
                let mut out = Vec::with_capacity(entries.len() * 2);
                for (key, value) in entries {
                    out.push(*key);
                    out.push(*value);
                }
                out
            }
            Some(ExprKind::Set { items }) => items.clone(),
            Some(ExprKind::New { count }) => count.iter().copied().collect(),
            Some(ExprKind::Assign { lhs, rhs, .. }) => {
                let mut out = vec![*rhs];
                // For index assignments, include container and index as children
                if let AssignLhs::Index { container, index } = lhs {
                    out.push(*container);
                    out.push(*index);
                }
                out
            }
            Some(ExprKind::Wrapper { expr }) => vec![*expr],
            Some(ExprKind::Cast { expr, .. }) => vec![*expr],
            Some(ExprKind::Missing) => vec![],
            Some(ExprKind::Boxed { expr }) => vec![*expr],
            Some(ExprKind::Deref { expr }) => vec![*expr],
            Some(ExprKind::Ref { expr }) => vec![*expr],
            Some(ExprKind::Tuple { elems }) => elems.clone(),
            Some(ExprKind::BinaryOp {
                lhs, rhs, operator, ..
            }) => {
                let mut out = Vec::with_capacity(3);
                out.push(*operator);
                out.push(*lhs);
                out.push(*rhs);
                out
            }
            Some(ExprKind::OpFunc { .. }) => vec![],
            Some(ExprKind::UnaryOp { operator, expr, .. }) => vec![*operator, *expr],
            Some(ExprKind::Index { container, index }) => vec![*container, *index],
            Some(ExprKind::StructLiteral { fields, .. }) => {
                fields.iter().map(|(_, id)| *id).collect()
            }
            Some(ExprKind::Some { expr }) => vec![*expr],
            Some(ExprKind::Range { start, end, .. }) => vec![*start, *end],
            Some(ExprKind::Nil)
            | Some(ExprKind::LiteralInt)
            | Some(ExprKind::LiteralIntSized(_))
            | Some(ExprKind::LiteralFloat)
            | Some(ExprKind::LiteralFloatSized)
            | Some(ExprKind::LiteralBool(_))
            | Some(ExprKind::LocalRef(_))
            | Some(ExprKind::DefRef(_))
            | Some(ExprKind::ScopedAccess { .. }) => {
                vec![]
            }
            _ => vec![],
        };
        out
    }

    /// Return the kind of an expression, if known.
    pub fn expr_kind(&self, expr: NodeId) -> Option<&ExprKind> {
        self.expr_records.get(&expr).map(|rec| &rec.kind)
    }

    /// Return the primary source info for an expression, if known.
    pub fn expr_src(&self, expr: NodeId) -> Option<&Source> {
        self.expr_records
            .get(&expr)
            .and_then(|rec| rec.source.as_ref())
    }
}

/// Options controlling the typechecking pipeline.
pub struct TypecheckOptions {
    /// When true, the pipeline may stop after the first error per module or
    /// binding group. Semantics are intentionally vague for now.
    pub stop_after_first_error: bool,
}

impl Default for TypecheckOptions {
    fn default() -> Self {
        TypecheckOptions {
            stop_after_first_error: false,
        }
    }
}

/// Classification and payload for type errors.
///
/// This is closely modeled on the existing type system's error representation,
/// but pared down slightly until we wire in richer info structures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeErrorKind {
    /// Free-form message for errors that do not yet have a more structured
    /// representation.
    Message(String),
    /// Assertion failures where some type was expected to satisfy an
    /// additional condition (used mainly for internal checks).
    Assertion(String, Ty),
    /// General type mismatch (including arity, constructor, or literal
    /// mismatches).
    Mismatch(Ty, Ty),
    /// Trait/impl signature mismatch (used when checking annotated impls).
    MismatchImpl(String, String, Ty, Ty),
    /// Types that were expected to be equal but are not.
    Equality(Ty, Ty),
    /// Expected a type to be an instance of another.
    InstanceOf(Ty, Ty),
    /// A type variable that could not be solved after solving and
    /// generalization.
    UnsolvableTyVar(TyVar),
    /// Unsolved or unsatisfiable predicate constraint (Class, HasField, Recv).
    Predicate(Predicate),
    /// Recursive unification attempt (would lead to an infinite type).
    RecursiveUnification(Ty, Ty),
    /// Attempted to unify a rigid (non-meta) type variable with an
    /// incompatible type.
    RigidVar(TyVar, Ty),
    /// Occurs check failure when trying to bind a type variable.
    OccursCheck(TyVar, Ty),
    /// Predicate requirement that could not be satisfied.
    MissingPredicate,
    /// Predicate resolved in multiple incomparable ways.
    AmbiguousPredicate,
    /// Predicate requirements that cannot both hold.
    DisjointPredicates,
    /// General unsolved predicate.
    UnsolvedPredicate,
    /// Skolem vs constant conflict.
    SkolemVersusConstant,
    /// Skolem vs skolem conflict.
    SkolemVersusSkolem,
    /// Skolem escaping its scope.
    EscapingSkolem,
    /// Rigid type variable conflicts.
    RigidTypeVariable,
    /// Generic unification failures.
    Unification,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
    pub info: TypeSystemInfo,
}

impl TypeError {
    pub fn message(msg: impl Into<String>, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Message(msg.into()),
            info,
        }
    }

    pub fn assertion(msg: impl Into<String>, ty: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Assertion(msg.into(), ty),
            info,
        }
    }

    pub fn mismatch(a: Ty, b: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Mismatch(a, b),
            info,
        }
    }

    pub fn mismatch_impl(
        kind: impl Into<String>,
        name: impl Into<String>,
        trait_ty: Ty,
        impl_ty: Ty,
        info: TypeSystemInfo,
    ) -> Self {
        TypeError {
            kind: TypeErrorKind::MismatchImpl(kind.into(), name.into(), trait_ty, impl_ty),
            info,
        }
    }

    pub fn equality(a: Ty, b: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Equality(a, b),
            info,
        }
    }

    pub fn tyvar(v: TyVar, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::UnsolvableTyVar(v),
            info,
        }
    }

    pub fn predicate(pred: Predicate, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Predicate(pred),
            info,
        }
    }

    pub fn missing_predicate(pred: Predicate, mut info: TypeSystemInfo) -> Self {
        info.missing_predicate(&pred);
        TypeError {
            kind: TypeErrorKind::MissingPredicate,
            info,
        }
    }

    pub fn recursive_unify(a: Ty, b: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::RecursiveUnification(a, b),
            info,
        }
    }

    pub fn rigid_var(var: TyVar, ty: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::RigidVar(var, ty),
            info,
        }
    }

    pub fn occurs_check(var: TyVar, ty: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::OccursCheck(var, ty),
            info,
        }
    }

    pub fn skolem_versus_constant(var: TyVar, ty: Ty, mut info: TypeSystemInfo) -> Self {
        info.escaped_skolems(&[var.clone()]);
        info.equality_type_pair(&Ty::Var(var.clone()), &ty);
        TypeError::from_info(TypeErrorKind::SkolemVersusConstant, info)
    }

    pub fn skolem_versus_skolem(a: TyVar, b: TyVar, mut info: TypeSystemInfo) -> Self {
        info.escaped_skolems(&[a.clone(), b.clone()]);
        info.equality_type_pair(&Ty::Var(a), &Ty::Var(b));
        TypeError::from_info(TypeErrorKind::SkolemVersusSkolem, info)
    }

    pub fn escaping_skolem(var: TyVar, ty: Ty, mut info: TypeSystemInfo) -> Self {
        info.escaped_skolems(&[var.clone()]);
        info.equality_type_pair(&Ty::Var(var), &ty);
        TypeError::from_info(TypeErrorKind::EscapingSkolem, info)
    }

    pub fn instance_of(a: Ty, b: Ty, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::InstanceOf(a, b),
            info,
        }
    }

    pub fn new(msg: impl Into<String>, info: TypeSystemInfo) -> Self {
        TypeError {
            kind: TypeErrorKind::Message(msg.into()),
            info,
        }
    }

    pub fn from_info(kind: TypeErrorKind, info: TypeSystemInfo) -> Self {
        TypeError { kind, info }
    }

    pub fn message_str(&self) -> String {
        match &self.kind {
            TypeErrorKind::Message(msg) => msg.clone(),
            TypeErrorKind::Assertion(expected, found) => {
                format!("expected {} type, but found {}", expected, found)
            }
            TypeErrorKind::Mismatch(a, b) => {
                format!("type mismatch: `{}` and `{}`", a, b)
            }
            TypeErrorKind::MismatchImpl(kind, name, trait_ty, impl_ty) => format!(
                "{} `{}` has an incompatible type for trait\nexpected signature `{}`\n   found signature `{}`",
                kind, name, trait_ty, impl_ty
            ),
            TypeErrorKind::Equality(a, b) => {
                format!("types `{}` and `{}` are not equal", a, b)
            }
            TypeErrorKind::InstanceOf(a, b) => {
                format!("type `{}` is not an instance of `{}`", a, b)
            }
            TypeErrorKind::UnsolvableTyVar(v) => {
                format!("type variable `{}` cannot be solved", v)
            }
            TypeErrorKind::Predicate(pred) => {
                let mut msg = format!("expression does not implement {}", pred);
                let mut seen_details = HashSet::new();
                for info in &self.info.info {
                    if let Info::Detail(detail) = info {
                        if seen_details.insert(detail) {
                            msg.push_str(&format!("\nnote: {}", detail));
                        }
                    }
                }
                msg
            }
            TypeErrorKind::RecursiveUnification(a, b) => {
                format!("recursive unification: {} and {}", a, b)
            }
            TypeErrorKind::RigidVar(var, ty) => {
                format!("cannot unify rigid type variable {} with {}", var, ty)
            }
            TypeErrorKind::OccursCheck(var, ty) => {
                format!("occurs check failed: {} occurs in {}", var, ty)
            }
            TypeErrorKind::MissingPredicate => {
                let mut msg = String::new();
                let mut first = true;
                let mut add_line = |msg: &mut String, line: &str| {
                    if line.is_empty() {
                        return;
                    }
                    if !first {
                        msg.push('\n');
                    }
                    first = false;
                    msg.push_str(line);
                };

                let mut consumed = Vec::new();
                let pred_info =
                    self.info
                        .info
                        .iter()
                        .enumerate()
                        .find_map(|(idx, info)| match info {
                            Info::MissingPredicate(Predicate::Class(class)) => Some((idx, class)),
                            _ => None,
                        });

                let scheme_info =
                    self.info
                        .info
                        .iter()
                        .enumerate()
                        .find_map(|(idx, info)| match info {
                            Info::SkolemizedTypeScheme(_, scheme) => Some((idx, scheme)),
                            _ => None,
                        });

                if let (Some((pred_idx, class)), Some((scheme_idx, scheme))) =
                    (pred_info, scheme_info)
                {
                    let recv = class
                        .args
                        .first()
                        .map(|t| t.to_string())
                        .unwrap_or_else(|| "<unknown>".into());
                    let suffix = if class.args.len() > 1 {
                        let params = class.args[1..]
                            .iter()
                            .map(|p| format!("`{}`", p))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(" with parameters [{}]", params)
                    } else {
                        String::new()
                    };

                    add_line(
                        &mut msg,
                        &format!(
                            "type `{}` in this signature\n  {}\ndoes not implement trait `{}`{}",
                            recv, scheme, class.path, suffix
                        ),
                    );
                    consumed.push(pred_idx);
                    consumed.push(scheme_idx);
                }

                for (idx, info) in self.info.info.iter().enumerate() {
                    if consumed.contains(&idx) {
                        continue;
                    }
                    add_line(&mut msg, &info.to_string());
                }

                msg
            }
            TypeErrorKind::AmbiguousPredicate
            | TypeErrorKind::DisjointPredicates
            | TypeErrorKind::UnsolvedPredicate
            | TypeErrorKind::SkolemVersusConstant
            | TypeErrorKind::SkolemVersusSkolem
            | TypeErrorKind::EscapingSkolem
            | TypeErrorKind::RigidTypeVariable
            | TypeErrorKind::Unification => {
                let mut msg = String::new();
                let mut first = true;
                let mut add_line = |msg: &mut String, line: &str| {
                    if line.is_empty() {
                        return;
                    }
                    if !first {
                        msg.push('\n');
                    }
                    first = false;
                    msg.push_str(line);
                };

                for info in &self.info.info {
                    add_line(&mut msg, &info.to_string());
                }

                msg
            }
        }
    }
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypeErrorKind::Message(msg) => write!(f, "{}", msg),
            TypeErrorKind::Assertion(msg, ty) => {
                write!(f, "{}: {}", msg, ty)
            }
            TypeErrorKind::Mismatch(a, b) => {
                write!(f, "type mismatch: `{}` and `{}`", a, b)
            }
            TypeErrorKind::MismatchImpl(kind, name, trait_ty, impl_ty) => write!(
                f,
                "{} `{}` has an incompatible type for trait (expected `{}`, found `{}`)",
                kind, name, trait_ty, impl_ty
            ),
            TypeErrorKind::Equality(a, b) => {
                write!(f, "types `{}` and `{}` are not equal", a, b)
            }
            TypeErrorKind::InstanceOf(a, b) => {
                write!(f, "type `{}` is not an instance of `{}`", a, b)
            }
            TypeErrorKind::UnsolvableTyVar(v) => {
                write!(f, "type variable `{}` cannot be solved", v)
            }
            TypeErrorKind::Predicate(pred) => {
                write!(f, "unsatisfied predicate: {}", pred)
            }
            TypeErrorKind::RecursiveUnification(a, b) => {
                write!(f, "recursive unification: {} and {}", a, b)
            }
            TypeErrorKind::RigidVar(var, ty) => {
                write!(f, "cannot unify rigid type variable {} with {}", var, ty)
            }
            TypeErrorKind::OccursCheck(var, ty) => {
                write!(f, "occurs check failed: {} occurs in {}", var, ty)
            }
            TypeErrorKind::MissingPredicate
            | TypeErrorKind::AmbiguousPredicate
            | TypeErrorKind::DisjointPredicates
            | TypeErrorKind::UnsolvedPredicate
            | TypeErrorKind::SkolemVersusConstant
            | TypeErrorKind::SkolemVersusSkolem
            | TypeErrorKind::EscapingSkolem
            | TypeErrorKind::RigidTypeVariable
            | TypeErrorKind::Unification => write!(f, "{}", self.message_str()),
        }
    }
}

/// Result of typechecking a single binding group.
#[derive(Clone, Debug)]
pub struct BindingGroupResult {
    pub errors: Vec<TypeError>,
}

/// Result of typechecking.
#[derive(Clone, Debug)]
pub struct TypeCheckResult {
    /// Type schemes for every definition from the input
    pub schemes: HashMap<DefId, TyScheme>,
    /// Monomorphic types for every expression node in the input
    pub node_tys: HashMap<NodeId, Ty>,
    /// Inferred types for local bindings (parameters, let-bindings, top-level assignments).
    /// Used by `inferred_local_type(LocalBindingId)` for cross-SCC type lookup when one
    /// definition references a local binding owned by another definition.
    pub local_tys: HashMap<LocalBindingId, Ty>,
    /// Resolved method calls, keyed by the call expression's NodeId.
    /// Populated by the solver when it resolves `ResolveMember` constraints.
    pub method_resolutions: HashMap<NodeId, MethodResolutionInfo>,
    /// All type errors discovered while typechecking
    pub errors: Vec<TypeError>,
}

#[derive(Clone, Debug, Default)]
struct SolverEnv {
    givens: Vec<Constraint>,
    metas: Vec<TyVar>,
}

/// Top-level entry point for typechecking.
///
/// Conceptually, this should:
/// - Build binding groups.
/// - For each group, build a constraint tree.
/// - Run the term solver (equalities/unification).
/// - Run the goal solver (traits, HasField, Recv).
/// - Apply defaulting, then generalization at the group boundary.
pub fn typecheck(
    input: &TypeCheckInput,
    _options: TypecheckOptions,
    tcx: &mut TyCtx,
    env: &dyn TypecheckEnv,
) -> TypeCheckResult {
    // Shared type context checking pass. This will accumulate information
    // across binding groups. Seed any pre-existing binding schemes from
    // the environment (e.g. annotated function types).
    let mut schema_allocator = SchemaVarAllocator::new();
    let mut ctx = SolverContext::new(&mut schema_allocator, env);
    log::debug!(
        "[typecheck] schema variable start: ?s{}",
        ctx.schema_allocator_mut().curr_id()
    );
    // Seed annotated schemes from the environment
    for def_id in input.def_nodes.keys() {
        if let Some(scheme) = env.external_scheme(*def_id) {
            ctx.binding_schemes.insert((*def_id).into(), scheme.clone());
            ctx.explicitly_annotated.insert((*def_id).into());
        }
    }

    let groups = input.binding_groups();

    let pretty_subst = tcx.inverted_var_subst();
    let BindingGroupResult { errors } =
        solve_groups(input, groups, &mut ctx, env, Some(&pretty_subst));

    let binding_schemes = mem::take(&mut ctx.binding_schemes);
    let mut node_tys = mem::take(&mut ctx.node_tys);
    let method_resolutions = mem::take(&mut ctx.method_resolutions);

    // At this point, solving + defaulting should have eliminated all unresolved
    // meta type variables from expression types. If any remain, treat it as a
    // type error so codegen never sees `Ty::Var(?t*)`.
    // push_unsolved_meta_tyvar_errors(&mut errors, module, &expr_types, &ctx.generalized_metas);

    tcx.node_tys.clear();
    for (expr_id, ty) in node_tys.iter() {
        tcx.node_tys.insert(*expr_id, ty.clone());
    }

    // Note: Path-based scheme storage in TyCtx is legacy. In the incremental
    // pipeline, schemes are stored by DefId in TypeCheckResult.
    tcx.schemes.clear();
    tcx.all_schemes.clear();

    let mut schemes = HashMap::new();
    let mut local_tys = HashMap::new();
    for (target, scheme) in binding_schemes.iter() {
        match target {
            BindingTarget::Def(def_id) => {
                // Store scheme by DefId in the result
                schemes.insert(*def_id, scheme.clone());
            }
            // Extract local binding types (monomorphic, so take the body type)
            BindingTarget::Local(local_id) => {
                local_tys.insert(*local_id, scheme.ty.clone());
            }
        }
    }

    // Copy pattern binding types to node_tys so that ty_of(node_id) works for
    // pattern nodes (parameters, let-bindings, etc.), not just expression nodes.
    for (node_id, pattern_record) in &input.pattern_records {
        match &pattern_record.kind {
            PatternKind::Binding { binding } | PatternKind::Deref { binding } => {
                if let Some(ty) = local_tys.get(binding) {
                    node_tys.insert(*node_id, ty.clone());
                }
            }
            PatternKind::Some { binding } => {
                // The `some(x)` pattern's type is nilable(inner_binding_ty)
                if let Some(inner_ty) = local_tys.get(binding) {
                    eprintln!(
                        "FOUND INNER TYPE FOR SOME BINDING: {:?} = {}",
                        binding, inner_ty
                    );
                    let nilable_ty = Ty::nilable(inner_ty.clone());
                    node_tys.insert(*node_id, nilable_ty);
                } else {
                    eprintln!("COULD NOT FIND INNER TYPE FOR SOME BINDING: {:?}", binding);
                }
            }
            _ => {}
        }
    }

    TypeCheckResult {
        schemes,
        node_tys,
        local_tys,
        method_resolutions,
        errors,
    }
}

#[allow(dead_code)]
fn push_unsolved_meta_tyvar_errors(
    errors: &mut Vec<TypeError>,
    module: &TypeCheckInput,
    expr_types: &HashMap<NodeId, Ty>,
    generalized_metas: &HashSet<TyVar>,
) {
    const MAX_SOURCES_PER_META: usize = 8;

    let mut info_by_var: HashMap<TyVar, TypeSystemInfo> = HashMap::new();

    for (expr_id, ty) in expr_types.iter() {
        let mut free_vars = HashSet::new();
        ty.free_ty_vars(&mut free_vars);

        if free_vars.is_empty() {
            continue;
        }

        let src = module
            .expr_records
            .get(expr_id)
            .and_then(|rec| rec.source.as_ref());

        for var in free_vars {
            if !var.is_unknown() || var.is_schema() {
                continue;
            }
            if generalized_metas.contains(&var) {
                continue;
            }

            let info = info_by_var
                .entry(var.clone())
                .or_insert_with(TypeSystemInfo::new);

            if let Some(src) = src {
                if info.source.len() < MAX_SOURCES_PER_META && !info.source.contains(src) {
                    info.with_src(src.clone());
                }
            }
        }
    }

    let mut vars: Vec<(TyVar, TypeSystemInfo)> = info_by_var.into_iter().collect();
    vars.sort_by(|(a, _), (b, _)| a.to_string().cmp(&b.to_string()));

    for (var, info) in vars {
        errors.push(TypeError::from_info(
            TypeErrorKind::UnsolvableTyVar(var),
            info,
        ));
    }
}

fn push_defaulting_outcome_errors(
    errors: &mut Vec<TypeError>,
    module: &TypeCheckInput,
    expr_types: &HashMap<NodeId, Ty>,
    generalized_metas: &HashSet<TyVar>,
    log: &DefaultingLog,
) {
    const MAX_SOURCES_PER_META: usize = 8;

    let mut vars_of_interest = HashSet::new();
    for entry in &log.entries {
        if matches!(entry.kind, DefaultingOutcomeKind::RejectedAmbiguous { .. }) {
            vars_of_interest.insert(entry.var.clone());
        }
    }
    if vars_of_interest.is_empty() {
        return;
    }

    let mut info_by_var: HashMap<TyVar, TypeSystemInfo> = HashMap::new();
    for (expr_id, ty) in expr_types.iter() {
        let mut free_vars = HashSet::new();
        ty.free_ty_vars(&mut free_vars);

        if free_vars.is_empty() {
            continue;
        }

        let src = module
            .expr_records
            .get(expr_id)
            .and_then(|rec| rec.source.as_ref());

        for var in free_vars {
            if !var.is_unknown() || var.is_schema() {
                continue;
            }
            if generalized_metas.contains(&var) {
                continue;
            }
            if !vars_of_interest.contains(&var) {
                continue;
            }

            let info = info_by_var
                .entry(var.clone())
                .or_insert_with(TypeSystemInfo::new);

            if let Some(src) = src {
                if info.source.len() < MAX_SOURCES_PER_META && !info.source.contains(src) {
                    info.with_src(src.clone());
                }
            }
        }
    }

    for entry in &log.entries {
        let DefaultingOutcomeKind::RejectedAmbiguous { candidates } = &entry.kind else {
            continue;
        };

        let info = info_by_var
            .get(&entry.var)
            .cloned()
            .unwrap_or_else(TypeSystemInfo::new);

        let candidates_str = candidates
            .iter()
            .map(|ty| ty.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        errors.push(TypeError::message(
            format!(
                "type defaulting is ambiguous for {}: multiple viable defaults ({})",
                entry.var, candidates_str
            ),
            info,
        ));
    }
}

/// Typecheck a single binding group.
///
/// This is the core typechecking entry point for incremental compilation.
/// It generates constraints for the group, solves them, applies defaulting,
/// and generalizes the resulting types.
///
/// # Arguments
/// * `input` - The typechecking input containing expression/pattern records
/// * `group` - The binding group to typecheck
/// * `external_schemes` - Callback for looking up schemes from previously-checked groups
/// * `ncx` - Name context for resolved paths
/// * `global_env` - Global environment with struct/trait definitions
///
/// # Returns
/// A `TypeCheckResult` containing inferred schemes, expression types, and errors.
pub fn typecheck_group<'a>(
    input: &TypeCheckInput,
    group: &BindingGroup<DefId>,
    external_schemes: impl Fn(&DefTarget) -> Option<TyScheme> + 'a,
    env: &'a dyn TypecheckEnv,
) -> TypeCheckResult {
    let mut schema_allocator = SchemaVarAllocator::new();
    let mut ctx = SolverContext::new(&mut schema_allocator, env);

    // Set up external scheme lookup callback
    ctx.set_external_schemes(external_schemes);

    // Seed context with annotated schemes for bindings in this group.
    // Annotated schemes come from the environment (TypecheckEnv::external_scheme).
    for def_id in &group.bindings {
        if let Some(scheme) = env.external_scheme(*def_id) {
            ctx.binding_schemes.insert((*def_id).into(), scheme.clone());
            ctx.explicitly_annotated.insert((*def_id).into());
        }
    }

    let errors = solve_single_group(input, group, &mut ctx, env, None);

    // Extract results
    let mut schemes = HashMap::new();
    let mut local_tys = HashMap::new();
    for (target, scheme) in ctx.binding_schemes.iter() {
        match target {
            BindingTarget::Def(def_id) => {
                if group.bindings.contains(def_id) {
                    schemes.insert(*def_id, scheme.clone());
                }
            }
            BindingTarget::Local(local_id) => {
                // Local bindings have monomorphic types, extract from scheme body
                local_tys.insert(*local_id, scheme.ty.clone());
            }
        }
    }

    // Populate node_tys for binding nodes from binding_schemes.
    // This mimics the legacy node_bindings loop that populated node_schemes.
    // We need both DEF sites (from pattern_records) and USE sites (from local_bindings_for_group).

    // DEF sites: pattern definitions (parameters, let-bindings, etc.)
    // Note: PatternKind::Some is handled during constraint generation
    // (apply_pattern_guard_with_ty) which correctly sets both outer and inner
    // types. We skip it here to avoid overwriting the outer type.
    for (node_id, record) in &input.pattern_records {
        let local_id = match &record.kind {
            PatternKind::Binding { binding } => Some(*binding),
            PatternKind::Deref { binding } => Some(*binding),
            PatternKind::Some { .. } => None, // handled during constraint generation
            PatternKind::Tuple { .. }
            | PatternKind::Field { .. }
            | PatternKind::Index { .. }
            | PatternKind::Missing => None,
        };
        if let Some(local_id) = local_id {
            if let Some(scheme) = ctx.binding_schemes.get(&local_id.into()) {
                ctx.node_tys.insert(*node_id, scheme.ty.clone());
            }
        }
    }

    // USE sites: references to local bindings (e.g., using a variable in an expression)
    for (node_id, local_id) in env.local_bindings_for_group() {
        if let Some(scheme) = ctx.binding_schemes.get(&local_id.into()) {
            ctx.node_tys.insert(node_id, scheme.ty.clone());
        }
    }

    let node_tys = mem::take(&mut ctx.node_tys);
    let method_resolutions = mem::take(&mut ctx.method_resolutions);

    TypeCheckResult {
        schemes,
        node_tys,
        local_tys,
        method_resolutions,
        errors,
    }
}

/// Internal helper to solve a single group, mutating the context.
fn solve_single_group(
    input: &TypeCheckInput,
    group: &BindingGroup<DefId>,
    ctx: &mut SolverContext,
    env: &dyn TypecheckEnv,
    pretty_subst: Option<&Subst>,
) -> Vec<TypeError> {
    let mut errors = vec![];

    let mut root = build_constraint_tree_for_group(input, ctx, group);
    log::debug!("[typecheck_group] constraints before solving");
    let mut depth = 0;
    walk_tree(&root, &mut |item| {
        if matches!(
            item,
            ConstraintTreeWalkItem::NodeEnd(_) | ConstraintTreeWalkItem::BindingNodeEnd(_)
        ) {
            depth -= 1;
        }
        log::debug!("  {}{}", " ".repeat(depth), item);
        if matches!(
            item,
            ConstraintTreeWalkItem::NodeStart(_) | ConstraintTreeWalkItem::BindingNodeStart(_)
        ) {
            depth += 1;
        }
    });

    let solve_env = SolverEnv::default();
    let mut subst = Subst::new();
    let residuals = solve_bindings(
        input,
        &mut root,
        &group.bindings,
        ctx,
        &solve_env,
        &mut subst,
        &mut errors,
    );
    let DefaultingResult {
        subst: defaulted_subst,
        residuals,
        log,
    } = apply_defaulting(input, ctx, group, env, residuals, &subst);
    subst = defaulted_subst;
    ctx.apply_subst(&subst);
    push_defaulting_outcome_errors(
        &mut errors,
        input,
        &ctx.node_tys,
        &ctx.generalized_metas,
        &log,
    );

    // Defaulting can refine metas in residual predicates (e.g. `Int[?t]`
    // becomes `Int[int]`). Re-run goal solving after defaulting so that
    // newly-concrete predicates can be discharged by instances.
    let post_defaulting =
        goal_solver::solve_constraints(&residuals, &solve_env.givens, &mut subst, ctx);
    ctx.apply_subst(&subst);
    log::debug!("[typecheck_group] subst: {:#}", subst);
    check_residuals_and_emit_errors(&post_defaulting.unsolved, ctx, pretty_subst, &mut errors);

    errors
}

fn solve_groups(
    input: &TypeCheckInput,
    groups: Vec<BindingGroup<DefId>>,
    ctx: &mut SolverContext,
    env: &dyn TypecheckEnv,
    pretty_subst: Option<&Subst>,
) -> BindingGroupResult {
    let mut errors = vec![];
    for group in groups.iter() {
        errors.extend(solve_single_group(input, group, ctx, env, pretty_subst));
    }
    BindingGroupResult { errors }
}

fn solve_bindings(
    module: &TypeCheckInput,
    root: &mut ConstraintNode,
    bindings: &[DefId],
    ctx: &mut SolverContext,
    solve_env: &SolverEnv,
    subst: &mut Subst,
    errors: &mut Vec<TypeError>,
) -> Vec<Constraint> {
    let residuals = solve_node(module, root, ctx, solve_env, subst, errors);
    let gen_result = generalize_group(module, ctx, bindings, &solve_env.metas, residuals, subst);
    for meta in gen_result.closing_subst.keys() {
        ctx.generalized_metas.insert(meta.clone());
    }
    for (def_id, scheme) in gen_result.schemes {
        ctx.binding_schemes.insert(def_id.into(), scheme);
        let skolem_subst = ctx.skolem_to_schema_subst(def_id);
        if !skolem_subst.is_empty() {
            ctx.apply_subst(&skolem_subst);
            subst.union(skolem_subst);
        }
        ctx.clear_skolems(def_id);
    }
    gen_result.residuals
}

/// Solve local bindings (let-bindings inside functions).
/// Local bindings don't get full generalization - they just get mono schemes.
fn solve_local_bindings(
    module: &TypeCheckInput,
    root: &mut ConstraintNode,
    bindings: &[LocalBindingId],
    ctx: &mut SolverContext,
    solve_env: &SolverEnv,
    subst: &mut Subst,
    errors: &mut Vec<TypeError>,
) -> Vec<Constraint> {
    let residuals = solve_node(module, root, ctx, solve_env, subst, errors);
    // Local bindings get mono schemes - no generalization
    for local_id in bindings {
        if let Some(scheme) = ctx.binding_schemes.get(&(*local_id).into()) {
            let mut instantiated = scheme.clone();
            instantiated.apply_subst(subst);
            ctx.binding_schemes
                .insert((*local_id).into(), TyScheme::from_mono(instantiated.ty));
        }
    }
    residuals
}

fn solve_node(
    module: &TypeCheckInput,
    node: &mut ConstraintNode,
    ctx: &mut SolverContext,
    solve_env: &SolverEnv,
    subst: &mut Subst,
    errors: &mut Vec<TypeError>,
) -> Vec<Constraint> {
    let mut solve_env = solve_env.clone();
    solve_env.givens.extend(node.givens.iter().cloned());
    solve_env.metas.extend(node.metas.iter().cloned());

    let new_constraints = instantiate_wanteds_into_equalities(&mut node.wanteds, ctx);
    node.wanteds.extend(new_constraints);

    for wanted in &node.wanteds {
        log::debug!("[solve_node] Wanted({})", wanted);
    }

    let term_result = term_solver::solve_equalities(&node.wanteds, subst);
    errors.extend(term_result.errors);
    node.apply_subst(subst);

    let goal_result = goal_solver::solve_constraints(&node.wanteds, &solve_env.givens, subst, ctx);
    let mut residuals = goal_result.unsolved;
    solve_env.givens.extend(goal_result.solved);

    for binding_node in &mut node.binding_nodes {
        let child_residuals = solve_local_bindings(
            module,
            &mut binding_node.root,
            &binding_node.bindings,
            ctx,
            &solve_env,
            subst,
            errors,
        );

        residuals.extend(child_residuals);
    }

    for child in &mut node.children {
        let child_residuals = solve_node(module, child, ctx, &solve_env, subst, errors);
        residuals.extend(child_residuals);
    }

    let goal_result = goal_solver::solve_constraints(&residuals, &solve_env.givens, subst, ctx);
    goal_result.unsolved
}

fn instantiate_wanteds_into_equalities(
    wanteds: &mut [Constraint],
    ctx: &mut SolverContext,
) -> Vec<Constraint> {
    let mut new_qualifiers = vec![];
    for wanted in wanteds {
        let ConstraintKind::Instantiate(inst) = &wanted.kind else {
            continue;
        };

        let scheme = match &inst.target {
            InstantiateTarget::Def(target) => ctx
                .lookup_def_scheme(target)
                .unwrap_or_else(|| panic!("cannot find scheme for def: {:?}", target)),
            InstantiateTarget::Local(binding_id) => {
                // First check local binding_schemes (same SCC)
                if let Some(scheme) = ctx.binding_schemes.get(&(*binding_id).into()).cloned() {
                    scheme
                } else {
                    // Cross-SCC local binding lookup via environment
                    let external_ty =
                        ctx.env()
                            .external_local_type(*binding_id)
                            .unwrap_or_else(|| {
                                panic!("cannot find scheme for local binding: {:?}", binding_id)
                            });
                    // Local bindings are monomorphic (no quantified variables)
                    TyScheme::from_mono(external_ty)
                }
            }
        };

        let (inst_ty, qualifiers) =
            instantiate_scheme_for_use(&scheme, inst.receiver_subst.as_ref(), ctx, &wanted.info);
        new_qualifiers.extend(qualifiers);
        log::debug!(
            "[instantiate_wanteds_into_equalities] target = {:?}, scheme = {}, inst_ty = {}",
            inst.target,
            scheme,
            inst_ty
        );
        *wanted = Constraint::eq(inst.ty.clone(), inst_ty, wanted.info.clone());
    }
    new_qualifiers
}

/// Instantiate a binding's scheme for a particular use site, as described in
/// the binding rules in docs/type-system.md Section 4.3.
fn instantiate_scheme_for_use(
    scheme: &TyScheme,
    receiver_subst: Option<&Subst>,
    ctx: &mut SolverContext,
    info: &TypeSystemInfo,
) -> (Ty, Vec<Constraint>) {
    let mut ty = scheme.ty.clone();
    let mut qualifiers = scheme.qualifiers.clone();
    if let Some(receiver_subst) = receiver_subst {
        log::debug!(
            "[instantiate_scheme_for_use] receiver_subst = {}",
            receiver_subst
        );
        ty.apply_subst(&receiver_subst);
        for pred in &mut qualifiers {
            pred.apply_subst(&receiver_subst);
        }
    } else {
        log::debug!("[instantiate_scheme_for_use] no receiver subst");
    }

    let mut subst = Subst::new();
    for v in scheme.vars.iter() {
        subst.insert(v.clone(), ctx.fresh_meta());
    }

    log::debug!(
        "[instantiate_scheme_for_use] scheme = {}, subst ={}",
        scheme,
        subst
    );
    ty.apply_subst(&subst);
    let qualifiers = qualifiers
        .into_iter()
        .map(|mut pred| {
            pred.apply_subst(&subst);
            Constraint::from_predicate(pred, info.clone())
        })
        .collect::<Vec<_>>();

    (ty, qualifiers)
}

fn check_residuals_and_emit_errors(
    residuals: &[Constraint],
    ctx: &SolverContext,
    pretty_subst: Option<&Subst>,
    errors: &mut Vec<TypeError>,
) {
    for pred in residuals {
        let mut info = pred.info.clone();
        if let ConstraintKind::ResolveMember(resolve_call) = &pred.kind {
            let (args, ret_ty) = match resolve_call.expected_ty.try_borrow_fn() {
                Ok((param_tys, ret_ty)) => {
                    let args = param_tys
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    (args, ret_ty.to_string())
                }
                Err(_) => ("<unknown>".to_string(), "<unknown>".to_string()),
            };

            match &resolve_call.kind {
                MemberAccessKind::InstanceCall => {
                    // Only attempt method availability/ambiguity diagnostics once
                    // the receiver type is headed; otherwise we don't know which
                    // receiver type to search.
                    let mut ty = resolve_call.subject_ty.clone();
                    let subject_fqn = loop {
                        match ty {
                            Ty::Ref(inner) | Ty::RawPtr(inner) => ty = (*inner).clone(),
                            Ty::Const(p) | Ty::Proj(p, _) => break Some(p),
                            Ty::Var(v) if v.is_meta() => break None,
                            _ => break None,
                        }
                    };

                    if let Some(subject_fqn) = subject_fqn {
                        let mut inherent_candidates = Vec::new();
                        for impl_ty in ctx.env().inherent_impls(&subject_fqn) {
                            for field in &impl_ty.fields {
                                let Some(name) = field.path.item_name() else {
                                    continue;
                                };
                                if name != resolve_call.member_name || field.is_static {
                                    continue;
                                }
                                inherent_candidates.push(field.path.to_string());
                            }
                        }

                        let mut trait_candidates = Vec::new();
                        for trait_ty in ctx.env().all_traits() {
                            if let Some(field) = trait_ty.get_field(&resolve_call.member_name) {
                                if field.is_static {
                                    continue;
                                }
                                trait_candidates.push(format!(
                                    "{}::{}",
                                    trait_ty.path, resolve_call.member_name
                                ));
                            }
                        }

                        inherent_candidates.sort();
                        inherent_candidates.dedup();
                        trait_candidates.sort();
                        trait_candidates.dedup();

                        let total_candidates = inherent_candidates.len() + trait_candidates.len();
                        if total_candidates == 0 {
                            let msg = format!(
                                "no method named `{}` found for `{}`",
                                resolve_call.member_name, resolve_call.subject_ty
                            );
                            errors.push(TypeError::message(msg, info));
                            continue;
                        }

                        if total_candidates > 1 {
                            let mut msg = format!(
                                "ambiguous method call: multiple candidates for `{}.{}`",
                                resolve_call.subject_ty, resolve_call.member_name
                            );
                            if !inherent_candidates.is_empty() {
                                msg.push_str(&format!(
                                    "\n  inherent: {}",
                                    inherent_candidates.join(", ")
                                ));
                            }
                            if !trait_candidates.is_empty() {
                                msg.push_str(&format!(
                                    "\n  trait: {}",
                                    trait_candidates.join(", ")
                                ));
                            }
                            errors.push(TypeError::message(msg, info));
                            continue;
                        }
                    }

                    let msg = format!(
                        "cannot resolve method call: `{}.{}` with signature: ({}) -> {}",
                        resolve_call.subject_ty, resolve_call.member_name, args, ret_ty
                    );
                    errors.push(TypeError::message(msg, info));
                    continue;
                }
                MemberAccessKind::ScopedCall { .. } => {
                    // For scoped calls, use the member name and subject type for error messages.
                    let msg = format!(
                        "cannot resolve scoped call: `{}::{}` with signature: ({}) -> {}",
                        resolve_call.subject_ty, resolve_call.member_name, args, ret_ty
                    );
                    errors.push(TypeError::message(msg, info));
                    continue;
                }
                MemberAccessKind::ScopedAccess { .. } => {
                    // For scoped member access (non-call), report as member access failure.
                    let msg = format!(
                        "cannot resolve scoped member access: `{}::{}`",
                        resolve_call.subject_ty, resolve_call.member_name
                    );
                    errors.push(TypeError::message(msg, info));
                    continue;
                }
            };
        }

        if let Some(kind) = pred.to_predicate() {
            info.unsolved_predicate(&kind, &pred.info);
            if let Some(failure) = ctx
                .predicate_failures
                .iter()
                .find(|entry| entry.wanted == *pred)
            {
                match failure.instance_failure.status {
                    InstanceFailureStatus::NoMatchingImpl => {
                        info.predicate_failure_detail(format!(
                            "no matching impls found for {}",
                            kind
                        ));
                    }
                    InstanceFailureStatus::HeadMatchFailed => {
                        for candidate in &failure.instance_failure.failures {
                            let details = candidate
                                .unsatisfied
                                .iter()
                                .map(|c| c.kind.to_string())
                                .collect::<Vec<_>>()
                                .join(", ");
                            let mut pretty_head = candidate.impl_head.clone();
                            if let Some(subst) = pretty_subst {
                                pretty_head.apply_subst(subst);
                            }
                            let msg = format!(
                                "unsatisfied prerequisites: {} from impl {}",
                                details, pretty_head
                            );
                            info.predicate_failure_detail(msg);
                        }
                    }
                    InstanceFailureStatus::Deferred => {}
                }
            }
            let skolem_infos = predicate_skolem_infos(&kind, ctx);
            if !skolem_infos.is_empty() {
                for sk_info in skolem_infos {
                    info.extend(sk_info);
                }
                errors.push(TypeError::missing_predicate(kind, info));
            } else {
                errors.push(TypeError::predicate(kind, info));
            }
        } else {
            let msg = format!("unsolved constraint: {}", pred.kind);
            errors.push(TypeError::message(msg, info));
        }
    }
}

fn predicate_skolem_infos(pred: &Predicate, ctx: &SolverContext) -> Vec<TypeSystemInfo> {
    let mut infos = Vec::new();
    for var in collect_predicate_vars(pred) {
        if let Some(meta) = ctx.skolem_info(&var) {
            infos.push(meta.info.clone());
        }
    }
    infos
}

fn collect_predicate_vars(pred: &Predicate) -> HashSet<TyVar> {
    let mut vars = HashSet::new();
    match pred {
        Predicate::Class(cp) => {
            for arg in &cp.args {
                arg.free_ty_vars(&mut vars);
            }
        }
        Predicate::HasField(hp) => {
            hp.record_ty.free_ty_vars(&mut vars);
            hp.field_ty.free_ty_vars(&mut vars);
        }
        Predicate::Recv(rp) => {
            rp.recv_ty.free_ty_vars(&mut vars);
            rp.expr_ty.free_ty_vars(&mut vars);
        }
    };

    vars
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefId,
        file_id::FileId,
        local_binding::LocalBindingId,
        node_id::NodeId,
        pathlib::ItemPath,
        resolution::DefTarget,
        ty::{SchemaVarAllocator, Ty},
    };

    use crate::{
        ExprRecord, PatternKind, PatternRecord, SolverEnv, TypeCheckInput, TypecheckOptions,
        binding_groups::{BindingGraph, BindingGroup},
        constraint_tree::{build_constraint_tree_for_group, walk_tree},
        context::{AssignLhs, ExprKind, LhsPattern, Pattern, SolverContext},
        env::GlobalEnv,
        mocks::MockTypecheckEnv,
        solve_bindings, solve_groups,
        tyctx::TyCtx,
        typecheck,
        types::{ImplKind, ImplTy, NominalKind, StructTy, Subst, TraitTy, TyScheme},
    };

    fn make_single_binding_module(
        def_id: DefId,
        root_expr: NodeId,
        kinds: HashMap<NodeId, ExprKind>,
    ) -> TypeCheckInput {
        let mut graph = BindingGraph::<DefId>::new();
        graph.add_binding(def_id);

        let mut def_nodes = HashMap::new();
        def_nodes.insert(def_id, root_expr);

        let expr_records = kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        TypeCheckInput {
            bindings: graph,
            def_nodes,
            file_main_stmts: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            lowering_errors: Vec::new(),
        }
    }

    #[test]
    fn typecheck_if_expression_succeeds() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let cond = NodeId::new();
        let then_expr = NodeId::new();
        let else_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(cond, ExprKind::LiteralBool(true));
        kinds.insert(then_expr, ExprKind::LiteralBool(true));
        kinds.insert(else_expr, ExprKind::LiteralBool(false));
        kinds.insert(
            expr_id,
            ExprKind::If {
                cond,
                then_branch: then_expr,
                else_branch: Some(else_expr),
            },
        );

        let module = make_single_binding_module(def_id, expr_id, kinds);
        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let typecheck_env = MockTypecheckEnv::new();
        let result = typecheck(&module, options, &mut ty_ctx, &typecheck_env);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn typecheck_while_expression_succeeds() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let cond = NodeId::new();
        let body_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(cond, ExprKind::LiteralBool(true));
        kinds.insert(body_expr, ExprKind::LiteralBool(true));
        kinds.insert(
            expr_id,
            ExprKind::While {
                cond,
                body: body_expr,
            },
        );

        let module = make_single_binding_module(def_id, expr_id, kinds);

        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let typecheck_env = MockTypecheckEnv::new();
        let result = typecheck(&module, options, &mut ty_ctx, &typecheck_env);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn typecheck_pattern_if_nilable_succeeds() {
        let def_id = DefId::new(FileId(0), 0);
        let local_binding_id = LocalBindingId::new(def_id, 5);
        let _guard = NodeId::enter_def(def_id);
        let scrutinee = NodeId::new();
        let then_expr = NodeId::new();
        let else_expr = NodeId::new();
        let expr_id = NodeId::new();
        let outer_pattern_id = NodeId::new();
        let inner_pattern_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(scrutinee, ExprKind::Nil);
        kinds.insert(then_expr, ExprKind::LiteralBool(true));
        kinds.insert(else_expr, ExprKind::LiteralBool(false));
        kinds.insert(
            expr_id,
            ExprKind::IfPattern {
                scrutinee,
                pattern: Pattern::Some {
                    outer_node_id: outer_pattern_id,
                    inner_node_id: inner_pattern_id,
                    local_id: local_binding_id,
                },
                then_branch: then_expr,
                else_branch: Some(else_expr),
            },
        );

        let module = make_single_binding_module(def_id, expr_id, kinds);

        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let typecheck_env = MockTypecheckEnv::new();
        let result = typecheck(&module, options, &mut ty_ctx, &typecheck_env);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn typecheck_loop_with_break_succeeds() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let break_expr = NodeId::new();
        let loop_expr = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(break_expr, ExprKind::LiteralBool(true));
        kinds.insert(loop_expr, ExprKind::Loop { body: break_expr });

        let module = make_single_binding_module(def_id, loop_expr, kinds);

        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let typecheck_env = MockTypecheckEnv::new();
        let result = typecheck(&module, options, &mut ty_ctx, &typecheck_env);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn typecheck_struct_literal_with_hasfield_succeeds() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let field_expr = NodeId::new();
        let expr_id = NodeId::new();

        let mut kinds = HashMap::new();
        kinds.insert(field_expr, ExprKind::LiteralBool(true));
        kinds.insert(
            expr_id,
            ExprKind::StructLiteral {
                path: "A".into(),
                fields: vec![("x".to_string(), field_expr)],
            },
        );

        let module = make_single_binding_module(def_id, expr_id, kinds);

        // Build a MockTypecheckEnv with a struct A { x: bool } so HasField can succeed.
        let struct_path = ItemPath::from("A");
        let bool_scheme = TyScheme::from_mono(Ty::bool());
        let struct_ty = StructTy {
            kind: NominalKind::Struct,
            path: struct_path.clone(),
            ty: TyScheme::from_mono(Ty::Const(struct_path.clone())),
            fields: vec![("x".to_string(), bool_scheme)],
        };

        let mut typecheck_env = MockTypecheckEnv::new();
        typecheck_env.add_struct(ItemPath::from("A"), struct_ty);

        let options = TypecheckOptions::default();

        let mut ty_ctx = TyCtx::new(GlobalEnv::new());
        let result = typecheck(&module, options, &mut ty_ctx, &typecheck_env);

        assert!(result.errors.is_empty());
    }

    #[test]
    fn solve_module_with_solve_bindings_basic_expression() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let root_expr = NodeId::new(); // { 1u32 }
        let mut kinds = HashMap::new();
        kinds.insert(root_expr, ExprKind::LiteralIntSized(Ty::u32()));

        let mut subst = Subst::new();
        let solve_env = SolverEnv::default();
        let typecheck_env = MockTypecheckEnv::new();
        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);

        let module = make_single_binding_module(def_id, root_expr, kinds);

        let group = BindingGroup {
            bindings: vec![def_id],
        };
        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| {
            println!("{}", item);
        });

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &[def_id],
            &mut ctx,
            &solve_env,
            &mut subst,
            &mut errors,
        );

        println!("residuals: {:?}", residuals);
        println!("subst: {:?}", subst);
        println!("errors: {:?}", errors);
    }

    #[test]
    fn solve_module_with_solve_bindings_if_else() {
        let def_id = DefId::new(FileId(0), 0);
        let _guard = NodeId::enter_def(def_id);
        let root_expr = NodeId::new(); // if/else
        let cond = NodeId::new();
        let then_branch = NodeId::new();
        let else_branch = NodeId::new();
        let mut kinds = HashMap::new();
        kinds.insert(cond, ExprKind::LiteralBool(true));
        kinds.insert(then_branch, ExprKind::LiteralIntSized(Ty::u32()));
        kinds.insert(else_branch, ExprKind::LiteralIntSized(Ty::u32()));
        kinds.insert(
            root_expr,
            ExprKind::If {
                cond,
                then_branch,
                else_branch: Some(else_branch),
            },
        );

        let mut subst = Subst::new();
        let env = SolverEnv::default();
        let typecheck_env = MockTypecheckEnv::new();
        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);

        let module = make_single_binding_module(def_id, root_expr, kinds);

        let group = BindingGroup {
            bindings: vec![def_id],
        };
        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| {
            println!("{}", item);
        });

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &[def_id],
            &mut ctx,
            &env,
            &mut subst,
            &mut errors,
        );

        println!("errors: {:?}", errors);
        println!("residuals: {:?}", residuals);
        println!("subst: {}", subst);
    }

    fn make_multi_binding_module(
        def_nodes: HashMap<DefId, NodeId>,
        expr_kinds: HashMap<NodeId, ExprKind>,
    ) -> TypeCheckInput {
        let mut graph = BindingGraph::<DefId>::new();
        for def_id in def_nodes.keys() {
            graph.add_binding(*def_id);
        }

        let expr_records = expr_kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        TypeCheckInput {
            bindings: graph,
            def_nodes,
            file_main_stmts: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            lowering_errors: Vec::new(),
        }
    }

    fn make_multi_binding_module_with_patterns(
        def_nodes: HashMap<DefId, NodeId>,
        expr_kinds: HashMap<NodeId, ExprKind>,
        pattern_records: HashMap<NodeId, PatternRecord>,
    ) -> TypeCheckInput {
        let mut graph = BindingGraph::<DefId>::new();
        for def_id in def_nodes.keys() {
            graph.add_binding(*def_id);
        }

        let expr_records = expr_kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        TypeCheckInput {
            bindings: graph,
            def_nodes,
            file_main_stmts: HashMap::new(),
            expr_records,
            pattern_records,
            lowering_errors: Vec::new(),
        }
    }

    #[test]
    fn solve_bindings_polymorphic_local_id_used_at_two_types() {
        //
        // Model:
        // fn main() {
        //   id = (x) => x
        //   a = id(1u32)
        //   b = id(true)
        // }

        // Top-level def id for main
        let main_def = DefId::new(FileId(0), 0);

        // Local binding ids (still use BindingId for locals)
        let id = LocalBindingId::new(main_def, 2); // local value binding inside main
        let x = LocalBindingId::new(main_def, 3); // closure parameter, nested under id
        let a = LocalBindingId::new(main_def, 4);
        let b = LocalBindingId::new(main_def, 5);

        let _guard = NodeId::enter_def(main_def);

        // Expression node ids
        let main_root = NodeId::new();
        let main_fn = NodeId::new();

        // id = (x) => x
        let id_body = NodeId::new();
        let id_closure = NodeId::new();
        let assign_id = NodeId::new();
        let pat_id = NodeId::new();

        // a = id(1u32)
        let call_u32 = NodeId::new();
        let callee_u32 = NodeId::new();
        let arg_u32 = NodeId::new();
        let assign_a = NodeId::new();
        let pat_a = NodeId::new();

        // b = id(true)
        let call_bool = NodeId::new();
        let callee_bool = NodeId::new();
        let arg_bool = NodeId::new();
        let assign_b = NodeId::new();
        let pat_b = NodeId::new();

        // Build def_nodes - maps DefId to root expression NodeId.
        let mut def_nodes: HashMap<DefId, NodeId> = HashMap::new();
        def_nodes.insert(main_def, main_fn);

        // Build expression kinds.
        let mut kinds: HashMap<NodeId, ExprKind> = HashMap::new();

        // Closure body: just returns the param.
        kinds.insert(id_body, ExprKind::LocalRef(x));

        // Closure expression itself.
        kinds.insert(
            id_closure,
            ExprKind::Closure {
                params: vec![x],
                body: id_body,
            },
        );

        // Assign that introduces local id.
        kinds.insert(
            assign_id,
            ExprKind::Assign {
                lhs_pattern: pat_id,
                lhs: AssignLhs::Pattern(LhsPattern::Binding(id)),
                rhs: id_closure,
            },
        );

        // a = id(1u32)
        kinds.insert(callee_u32, ExprKind::LocalRef(id));
        kinds.insert(arg_u32, ExprKind::LiteralIntSized(Ty::u32()));
        kinds.insert(
            call_u32,
            ExprKind::Call {
                callee: callee_u32,
                args: vec![arg_u32],
            },
        );
        kinds.insert(
            assign_a,
            ExprKind::Assign {
                lhs_pattern: pat_a,
                lhs: AssignLhs::Pattern(LhsPattern::Binding(a)),
                rhs: call_u32,
            },
        );

        // b = id(true)
        kinds.insert(callee_bool, ExprKind::LocalRef(id));
        kinds.insert(arg_bool, ExprKind::LiteralBool(true));
        kinds.insert(
            call_bool,
            ExprKind::Call {
                callee: callee_bool,
                args: vec![arg_bool],
            },
        );
        kinds.insert(
            assign_b,
            ExprKind::Assign {
                lhs_pattern: pat_b,
                lhs: AssignLhs::Pattern(LhsPattern::Binding(b)),
                rhs: call_bool,
            },
        );

        // main root sequences the assignments.
        kinds.insert(
            main_root,
            ExprKind::Sequence {
                items: vec![assign_id, assign_a, assign_b],
            },
        );
        // Wrap the main body in a Function expression so constraint generation
        // treats `main` as a function binding with a unit parameter list.
        kinds.insert(
            main_fn,
            ExprKind::Function {
                params: vec![],
                body: main_root,
            },
        );

        // Pattern records for the LHS bindings.
        let mut pattern_records: HashMap<NodeId, PatternRecord> = HashMap::new();
        pattern_records.insert(
            pat_id,
            PatternRecord {
                kind: PatternKind::Binding { binding: id },
                source: None,
            },
        );
        pattern_records.insert(
            pat_a,
            PatternRecord {
                kind: PatternKind::Binding { binding: a },
                source: None,
            },
        );
        pattern_records.insert(
            pat_b,
            PatternRecord {
                kind: PatternKind::Binding { binding: b },
                source: None,
            },
        );

        let module = make_multi_binding_module_with_patterns(def_nodes, kinds, pattern_records);

        // Solve the top-level group containing only `main`. The local binding `id`
        // must be solved and generalized before its uses in later statements.
        let group = BindingGroup {
            bindings: vec![main_def],
        };

        let mut subst = Subst::new();
        let env = SolverEnv::default();

        let typecheck_env = MockTypecheckEnv::new();
        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);

        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| println!("{}", item));

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &[main_def],
            &mut ctx,
            &env,
            &mut subst,
            &mut errors,
        );

        println!("errors: {:?}", errors);
        println!("residuals: {:?}", residuals);
        println!("subst: {}", subst);
        for (binding, scheme) in ctx.binding_schemes.iter() {
            println!("{:?}: {}", binding, scheme);
        }

        // No residual predicates expected for this program.
        assert!(
            residuals.is_empty(),
            "expected no residuals, got: {:?}",
            residuals
        );
    }

    #[test]
    fn solve_groups_int_literal_grounded_by_parameter_type() {
        // extern malloc(len: uint) -> rawptr[u8]
        // fn main() { malloc(10) }

        let malloc_def = DefId::new(FileId(0), 0);
        let main_def = DefId::new(FileId(0), 1);

        let _guard = NodeId::enter_def(main_def);

        let main_fn = NodeId::new();
        let main_root = NodeId::new();
        let malloc_callee = NodeId::new();
        let len_arg = NodeId::new();

        let malloc_scheme = TyScheme {
            vars: vec![],
            qualifiers: vec![],
            ty: Ty::func(vec![Ty::uint()], Ty::rawptr(Ty::u8())),
        };

        let int_trait_ty = TraitTy {
            path: ItemPath::from("core::Int"),
            ty: Ty::proj("core::Int", vec![Ty::var("'a")]),
            super_traits: vec![],
            fields: vec![],
            default_ty: None,
        };

        let uint_int_impl = ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::uint(),
                trait_ty: Ty::proj("core::Int", vec![Ty::uint()]),
                ty_args: vec![],
            },
            predicates: vec![],
            fields: vec![],
        };

        // def_nodes - maps DefId to root expression NodeId
        // Note: malloc is extern (no body), only main has a body
        let mut def_nodes: HashMap<DefId, NodeId> = HashMap::new();
        def_nodes.insert(main_def, main_fn);

        // Expressions
        let mut kinds: HashMap<NodeId, ExprKind> = HashMap::new();

        // fn main() { malloc(10) } where 10 is an unsized int literal that must be uint.
        kinds.insert(
            malloc_callee,
            ExprKind::DefRef(DefTarget::Workspace(malloc_def)),
        );
        kinds.insert(len_arg, ExprKind::LiteralInt);
        kinds.insert(
            main_root,
            ExprKind::Call {
                callee: malloc_callee,
                args: vec![len_arg],
            },
        );
        kinds.insert(
            main_fn,
            ExprKind::Function {
                params: vec![],
                body: main_root,
            },
        );

        let module = make_multi_binding_module(def_nodes, kinds);
        // Only main is in the binding group - malloc is extern with a known scheme
        let groups = vec![BindingGroup {
            bindings: vec![main_def],
        }];

        let mut typecheck_env = MockTypecheckEnv::new();
        typecheck_env.add_trait(ItemPath::from("core::Int"), int_trait_ty);
        typecheck_env.add_impl(uint_int_impl);
        // Add malloc's scheme to the environment so external_scheme() can find it
        typecheck_env.add_external_scheme(malloc_def, malloc_scheme.clone());

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);

        let result = solve_groups(&module, groups, &mut ctx, &typecheck_env, None);
        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );
    }

    #[test]
    fn solve_groups_int_literal_defaults() {
        // fn main() {
        //   x = 10
        //   ()
        // }
        //
        // Here `10` is an unsized int literal with no contextual type.
        // We expect it to be resolved via defaulting from the `core::Int` trait.
        // Note: We return `()` instead of `x` so the literal's type doesn't escape
        // into the function's return type (which would block defaulting due to
        // `will_be_generalized` check).

        // Top-level def id for main
        let main_def = DefId::new(FileId(0), 0);

        // Local binding id for x
        let x = LocalBindingId::new(main_def, 2);

        let _guard = NodeId::enter_def(main_def);

        // Expression node ids
        let main_fn = NodeId::new();
        let main_root = NodeId::new();
        let assign_x = NodeId::new();
        let pat_x = NodeId::new();
        let lit_10 = NodeId::new();
        let unit_lit = NodeId::new();

        // Build def_nodes - maps DefId to root expression NodeId.
        let mut def_nodes: HashMap<DefId, NodeId> = HashMap::new();
        def_nodes.insert(main_def, main_fn);

        // Build expression kinds.
        let mut kinds: HashMap<NodeId, ExprKind> = HashMap::new();

        // x = 10
        kinds.insert(lit_10, ExprKind::LiteralInt);
        kinds.insert(
            assign_x,
            ExprKind::Assign {
                lhs_pattern: pat_x,
                lhs: AssignLhs::Pattern(LhsPattern::Binding(x)),
                rhs: lit_10,
            },
        );

        // final expression is `()` (empty tuple)
        kinds.insert(unit_lit, ExprKind::Tuple { elems: vec![] });

        // Sequence the assignment and final value.
        kinds.insert(
            main_root,
            ExprKind::Sequence {
                items: vec![assign_x, unit_lit],
            },
        );

        // Wrap the main body in a Function expression so constraint generation
        // treats `main` as a function binding.
        kinds.insert(
            main_fn,
            ExprKind::Function {
                params: vec![],
                body: main_root,
            },
        );

        // Pattern record for `x` on the LHS.
        let mut pattern_records: HashMap<NodeId, PatternRecord> = HashMap::new();
        pattern_records.insert(
            pat_x,
            PatternRecord {
                kind: PatternKind::Binding { binding: x },
                source: None,
            },
        );

        let module = make_multi_binding_module_with_patterns(def_nodes, kinds, pattern_records);

        // MockTypecheckEnv: core::Int has a default type of `uint`, and there is an impl
        // Int[uint]. This should allow defaulting to pick `uint` for the literal.
        let mut typecheck_env = MockTypecheckEnv::new();

        let int_trait_ty = TraitTy {
            path: ItemPath::from("core::Int"),
            ty: Ty::proj("core::Int", vec![Ty::var("'a")]),
            super_traits: vec![],
            fields: vec![],
            default_ty: Some(Ty::uint()),
        };
        typecheck_env.add_trait(ItemPath::from("core::Int"), int_trait_ty);

        let uint_int_impl = ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::uint(),
                trait_ty: Ty::proj("core::Int", vec![Ty::uint()]),
                ty_args: vec![],
            },
            predicates: vec![],
            fields: vec![],
        };
        typecheck_env.add_impl(uint_int_impl);

        // Solve only the top-level group containing `main`. Local bindings are
        // solved via binding nodes under `main`.
        let groups = vec![BindingGroup {
            bindings: vec![main_def],
        }];

        let mut schema_allocator = SchemaVarAllocator::new();
        let mut ctx = SolverContext::new(&mut schema_allocator, &typecheck_env);

        let result = solve_groups(&module, groups, &mut ctx, &typecheck_env, None);
        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );

        // The literal should be defaulted to `uint`.
        let lit_ty = ctx
            .node_tys
            .get(&lit_10)
            .cloned()
            .unwrap_or_else(|| panic!("expected a type for literal node {:?}", lit_10));
        assert_eq!(lit_ty, Ty::uint());
    }
}
