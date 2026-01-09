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
pub mod path;
pub mod term_solver;
pub mod tyctx;
pub mod types;
pub mod unify;

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::rc::Rc;

use ray_shared::{
    collections::namecontext::NameContext,
    node_id::NodeId,
    pathlib::Path,
    span::Source,
    ty::{Ty, TyVar},
};

use crate::{
    binding_groups::{BindingGraph, BindingGroup, BindingId},
    constraint_tree::{
        ConstraintNode, ConstraintTreeWalkItem, build_constraint_tree_for_group, walk_tree,
    },
    constraints::{CallKind, Constraint, ConstraintKind, Predicate},
    context::{ExprKind, InstanceFailureStatus, SolverContext},
    defaulting::{DefaultingLog, DefaultingOutcomeKind, DefaultingResult, apply_defaulting},
    env::GlobalEnv,
    generalize::generalize_group,
    info::{Info, TypeSystemInfo},
    tyctx::TyCtx,
    types::{SchemaVarAllocator, Subst, Substitutable as _, TyScheme},
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
        params: Vec<BindingId>,
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
    Binding { binding: BindingId },
    /// Tuple or sequence pattern `(p1, ..., pn)` / `p1, ..., pn`.
    Tuple { elems: Vec<NodeId> },
    /// Field projection `base.field`.
    Field { base: NodeId, field: String },
    /// Index projection `container[index]`.
    Index { container: NodeId, index: NodeId },
    /// Dereference pattern `*x`.
    Deref { binding: BindingId },
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

pub struct ModuleInput {
    pub bindings: BindingGraph,
    /// Consolidated binding metadata keyed by `BindingId`. This gradually
    /// replaces the scattered binding_* maps as the pipeline is reworked.
    pub binding_records: HashMap<BindingId, BindingRecord>,
    /// Mapping from frontend node ids to lowered binding ids.
    pub node_bindings: HashMap<NodeId, NodeBinding>,
    /// Consolidated expression metadata keyed by NodeId, replacing the
    /// expr_kinds/expr_sources split as the new lowering pipeline lands.
    pub expr_records: HashMap<NodeId, ExprRecord>,
    /// Simplified pattern metadata so every AST pattern node can be typed.
    pub pattern_records: HashMap<NodeId, PatternRecord>,
    /// Shared allocator for schema variables so the frontend and solver
    /// agree on naming.
    pub schema_allocator: Rc<RefCell<SchemaVarAllocator>>,
    /// Errors recorded during lowering before the solver runs.
    pub lowering_errors: Vec<TypeError>,
}

impl ModuleInput {
    /// Compute binding groups for this module.
    ///
    /// - Walk the module's bindings and build a dependency graph over
    ///   `BindingId`.
    /// - Compute strongly connected components (SCCs) of this graph.
    /// - Return one `BindingGroup` per SCC, in a topologically sorted order
    ///   so groups can only depend on earlier groups.
    pub fn binding_groups(&self) -> Vec<BindingGroup> {
        let top_level: BTreeSet<BindingId> = self
            .binding_records
            .iter()
            .filter_map(|(bid, rec)| (!rec.is_extern && rec.parent.is_none()).then_some(*bid))
            .collect();

        self.bindings.compute_binding_groups_over(&top_level)
    }

    /// Return the root expression for a given binding, if any. Prefer the
    /// consolidated binding record and fall back to legacy state while the
    /// lowering pipeline is migrating.
    pub fn binding_root_expr(&self, id: BindingId) -> Option<NodeId> {
        let record = self.binding_records.get(&id);
        record.and_then(|record| record.body_expr)
    }

    /// Parent binding for the given binding id, if any.
    pub fn binding_parent(&self, id: BindingId) -> Option<BindingId> {
        self.binding_records
            .get(&id)
            .and_then(|record| record.parent)
    }

    /// Collect all bindings whose parent matches the provided id.
    pub fn bindings_with_parent(&self, parent: BindingId) -> Vec<BindingId> {
        self.binding_records
            .iter()
            .filter_map(|(id, record)| {
                if record.parent == Some(parent) {
                    Some(*id)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Determine the parent binding shared by all members of this group.
    pub fn group_parent(&self, group: &BindingGroup) -> Option<BindingId> {
        let mut parent: Option<BindingId> = None;
        for binding in &group.bindings {
            let this_parent = self.binding_parent(*binding);
            match (parent, this_parent) {
                (None, Some(p)) => parent = Some(p),
                (Some(existing), Some(p)) if existing != p => {
                    // Mixed-parent group; treat it as parentless.
                    debug_assert!(false, "mixed-parent group");
                    return None;
                }
                _ => {}
            }
        }
        parent
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
            Some(ExprKind::Assign { rhs, .. }) => vec![*rhs],
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
            | Some(ExprKind::BindingRef(_))
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

    pub fn schema_allocator(&self) -> Rc<RefCell<SchemaVarAllocator>> {
        self.schema_allocator.clone()
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
                            recv, scheme, class.name, suffix
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

/// Result of typechecking an entire module.
#[derive(Clone, Debug)]
pub struct TypeCheckResult {
    /// All type errors discovered while typechecking the module.
    pub errors: Vec<TypeError>,
}

#[derive(Clone, Debug, Default)]
struct SolverEnv {
    givens: Vec<Constraint>,
    metas: Vec<TyVar>,
}

/// Top-level entry point for typechecking a whole module.
///
/// Conceptually, this should:
/// - Build binding groups for the module.
/// - For each group, build a constraint tree.
/// - Run the term solver (equalities/unification).
/// - Run the goal solver (traits, HasField, Recv).
/// - Apply defaulting, then generalization at the group boundary.
pub fn check_module(
    module: &ModuleInput,
    _options: TypecheckOptions,
    tcx: &mut TyCtx,
    ncx: &NameContext,
) -> TypeCheckResult {
    // Shared type context for the module. This will accumulate information
    // across binding groups. Seed any pre-existing binding schemes from
    // the frontend (e.g. annotated function types).
    let mut ctx = SolverContext::new(module.schema_allocator.clone(), ncx, &tcx.global_env);
    log::debug!(
        "[check_module] schema variable start: ?s{}",
        ctx.schema_allocator_mut().curr_id()
    );
    for (binding_id, record) in module.binding_records.iter() {
        if let Some(scheme) = &record.scheme {
            ctx.binding_schemes.insert(*binding_id, scheme.clone());
            ctx.explicitly_annotated_bindings.insert(*binding_id);
        }
    }

    let groups = module.binding_groups();

    let pretty_subst = tcx.inverted_var_subst();
    let BindingGroupResult { errors } = solve_groups(
        module,
        groups,
        &mut ctx,
        &tcx.global_env,
        Some(&pretty_subst),
    );

    let binding_schemes = mem::take(&mut ctx.binding_schemes);
    let expr_types = mem::take(&mut ctx.expr_types);

    // At this point, solving + defaulting should have eliminated all unresolved
    // meta type variables from expression types. If any remain, treat it as a
    // type error so codegen never sees `Ty::Var(?t*)`.
    // push_unsolved_meta_tyvar_errors(&mut errors, module, &expr_types, &ctx.generalized_metas);

    tcx.node_tys.clear();
    for (expr_id, ty) in expr_types.iter() {
        tcx.node_tys.insert(*expr_id, ty.clone());
    }

    for (node_id, node_binding) in module.node_bindings.iter() {
        let binding_id = node_binding.binding();
        if let Some(scheme) = binding_schemes.get(&binding_id) {
            tcx.node_schemes.insert(*node_id, scheme.clone());
        }
    }

    tcx.schemes.clear();
    tcx.all_schemes.clear();
    for (binding_id, scheme) in binding_schemes.iter() {
        if let Some(record) = module.binding_records.get(binding_id) {
            if let Some(path) = &record.path {
                tcx.all_schemes.insert(path.clone(), scheme.clone());
                if !record.is_extern && record.parent.is_none() {
                    tcx.schemes.insert(path.clone(), scheme.clone());
                }
            }
        }
    }

    TypeCheckResult { errors }
}

#[allow(dead_code)]
fn push_unsolved_meta_tyvar_errors(
    errors: &mut Vec<TypeError>,
    module: &ModuleInput,
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
    module: &ModuleInput,
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

fn solve_groups(
    module: &ModuleInput,
    groups: Vec<BindingGroup>,
    ctx: &mut SolverContext,
    global_env: &GlobalEnv,
    pretty_subst: Option<&Subst>,
) -> BindingGroupResult {
    let mut errors = vec![];
    for group in groups.iter() {
        let mut root = build_constraint_tree_for_group(module, ctx, group);
        log::debug!("[solve_groups] constraints before solving");
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

        let env = SolverEnv::default();
        let mut subst = Subst::new();
        let residuals = solve_bindings(
            module,
            &mut root,
            &group.bindings,
            ctx,
            &env,
            global_env,
            &mut subst,
            &mut errors,
        );
        let DefaultingResult {
            subst: defaulted_subst,
            residuals,
            log,
        } = apply_defaulting(module, ctx, group, global_env, residuals, &subst);
        subst = defaulted_subst;
        ctx.apply_subst(&subst);
        push_defaulting_outcome_errors(
            &mut errors,
            module,
            &ctx.expr_types,
            &ctx.generalized_metas,
            &log,
        );

        // Defaulting can refine metas in residual predicates (e.g. `Int[?t]`
        // becomes `Int[int]`). Re-run goal solving after defaulting so that
        // newly-concrete predicates can be discharged by instances.
        let post_defaulting =
            goal_solver::solve_constraints(&residuals, &env.givens, global_env, &mut subst, ctx);
        ctx.apply_subst(&subst);
        log::debug!("[solve_groups] subst: {:#}", subst);
        check_residuals_and_emit_errors(
            module,
            &post_defaulting.unsolved,
            ctx,
            pretty_subst,
            &mut errors,
        );
    }

    BindingGroupResult { errors }
}

fn solve_bindings(
    module: &ModuleInput,
    root: &mut ConstraintNode,
    bindings: &[BindingId],
    ctx: &mut SolverContext,
    env: &SolverEnv,
    global_env: &GlobalEnv,
    subst: &mut Subst,
    errors: &mut Vec<TypeError>,
) -> Vec<Constraint> {
    let residuals = solve_node(module, root, ctx, env, global_env, subst, errors);
    let gen_result = generalize_group(module, ctx, bindings, &env.metas, residuals, subst);
    for meta in gen_result.closing_subst.keys() {
        ctx.generalized_metas.insert(meta.clone());
    }
    for (binding_id, scheme) in gen_result.schemes {
        ctx.binding_schemes.insert(binding_id, scheme);
        let skolem_subst = ctx.skolem_to_schema_subst_for_binding(binding_id);
        if !skolem_subst.is_empty() {
            ctx.apply_subst(&skolem_subst);
            subst.union(skolem_subst);
        }
        ctx.clear_skolems_for_binding(binding_id);
    }
    gen_result.residuals
}

fn solve_node(
    module: &ModuleInput,
    node: &mut ConstraintNode,
    ctx: &mut SolverContext,
    env: &SolverEnv,
    global_env: &GlobalEnv,
    subst: &mut Subst,
    errors: &mut Vec<TypeError>,
) -> Vec<Constraint> {
    let mut env = env.clone();
    env.givens.extend(node.givens.iter().cloned());
    env.metas.extend(node.metas.iter().cloned());

    let new_constraints = instantiate_wanteds_into_equalities(&mut node.wanteds, ctx);
    node.wanteds.extend(new_constraints);

    for wanted in &node.wanteds {
        log::debug!("[solve_node] Wanted({})", wanted);
    }

    let term_result = term_solver::solve_equalities(&node.wanteds, subst);
    errors.extend(term_result.errors);
    node.apply_subst(subst);

    let goal_result =
        goal_solver::solve_constraints(&node.wanteds, &env.givens, global_env, subst, ctx);
    let mut residuals = goal_result.unsolved;
    env.givens.extend(goal_result.solved);

    for binding_node in &mut node.binding_nodes {
        let child_residuals = solve_bindings(
            module,
            &mut binding_node.root,
            &binding_node.bindings,
            ctx,
            &env,
            global_env,
            subst,
            errors,
        );

        residuals.extend(child_residuals);
    }

    for child in &mut node.children {
        let child_residuals = solve_node(module, child, ctx, &env, global_env, subst, errors);
        residuals.extend(child_residuals);
    }

    let goal_result =
        goal_solver::solve_constraints(&residuals, &env.givens, global_env, subst, ctx);
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

        let Some(scheme) = ctx.binding_schemes.get(&inst.binding).cloned() else {
            panic!("cannot find scheme for binding: {:?}", inst.binding);
        };

        let (inst_ty, qualifiers) =
            instantiate_scheme_for_use(&scheme, inst.receiver_subst.as_ref(), ctx, &wanted.info);
        new_qualifiers.extend(qualifiers);
        log::debug!(
            "[instantiate_wanteds_into_equalities] binding = {:?}, scheme = {}, inst_ty = {}",
            inst.binding,
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
    module: &ModuleInput,
    residuals: &[Constraint],
    ctx: &SolverContext,
    pretty_subst: Option<&Subst>,
    errors: &mut Vec<TypeError>,
) {
    for pred in residuals {
        let mut info = pred.info.clone();
        if let ConstraintKind::ResolveCall(resolve_call) = &pred.kind {
            let (args, ret_ty) = match resolve_call.expected_fn_ty.try_borrow_fn() {
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
                CallKind::Instance => {
                    // Only attempt method availability/ambiguity diagnostics once
                    // the receiver type is headed; otherwise we don't know which
                    // receiver type to search.
                    let mut ty = resolve_call.subject_ty.clone();
                    let subject_fqn = loop {
                        match ty {
                            Ty::Ref(inner) | Ty::RawPtr(inner) => ty = (*inner).clone(),
                            Ty::Const(p) | Ty::Proj(p, _) => break Some(p.to_string()),
                            Ty::Var(v) if v.is_meta() => break None,
                            _ => break None,
                        }
                    };

                    if let Some(subject_fqn) = subject_fqn {
                        let mut inherent_candidates = Vec::new();
                        for impl_ty in ctx.global_env().inherent_impls_for_key(&subject_fqn) {
                            for field in &impl_ty.fields {
                                let Some(name) = field.path.name() else {
                                    continue;
                                };
                                if name != resolve_call.method_name || field.is_static {
                                    continue;
                                }
                                inherent_candidates.push(field.path.to_string());
                            }
                        }

                        let mut trait_candidates = Vec::new();
                        for trait_ty in ctx.global_env().traits.values() {
                            if let Some(field) = trait_ty.get_field(&resolve_call.method_name) {
                                if field.is_static {
                                    continue;
                                }
                                trait_candidates.push(format!(
                                    "{}::{}",
                                    trait_ty.path, resolve_call.method_name
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
                                resolve_call.method_name, resolve_call.subject_ty
                            );
                            errors.push(TypeError::message(msg, info));
                            continue;
                        }

                        if total_candidates > 1 {
                            let mut msg = format!(
                                "ambiguous method call: multiple candidates for `{}.{}`",
                                resolve_call.subject_ty, resolve_call.method_name
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
                        resolve_call.subject_ty, resolve_call.method_name, args, ret_ty
                    );
                    errors.push(TypeError::message(msg, info));
                    continue;
                }
                CallKind::Scoped { binding, .. } => {
                    let binding_name = module
                        .binding_records
                        .get(binding)
                        .and_then(|rec| rec.path.as_ref())
                        .map(|p| p.to_string())
                        .unwrap_or_else(|| binding.to_string());
                    let msg = format!(
                        "cannot resolve scoped call: `{}` on `{}` with signature: ({}) -> {}",
                        binding_name, resolve_call.subject_ty, args, ret_ty
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
    use super::*;
    use crate::binding_groups::{BindingGraph, BindingGroup, BindingId};
    use crate::context::{AssignLhs, ExprKind, LhsPattern, Pattern};
    use crate::types::{ImplKind, ImplTy, TraitTy, TyScheme};
    use crate::{BindingKind, BindingRecord, ExprRecord};
    use std::collections::HashMap;

    fn make_single_binding_module(
        binding_id: BindingId,
        root_expr: NodeId,
        kinds: HashMap<NodeId, ExprKind>,
    ) -> ModuleInput {
        let mut graph = BindingGraph::new();
        graph.add_binding(binding_id);

        let mut binding_records = HashMap::new();
        let mut record = BindingRecord::new(BindingKind::Value);
        record.body_expr = Some(root_expr);
        binding_records.insert(binding_id, record);

        let expr_records = kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        ModuleInput {
            bindings: graph,
            binding_records,
            node_bindings: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            schema_allocator: Rc::new(RefCell::new(SchemaVarAllocator::new())),
            lowering_errors: Vec::new(),
        }
    }

    #[test]
    fn check_module_if_expression_succeeds() {
        let binding_id = BindingId(3);
        let cond = NodeId(30);
        let then_expr = NodeId(31);
        let else_expr = NodeId(32);
        let expr_id = NodeId(3);

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

        let module = make_single_binding_module(binding_id, expr_id, kinds);
        let ncx = NameContext::new();
        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let result = check_module(&module, options, &mut ty_ctx, &ncx);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn check_module_while_expression_succeeds() {
        let binding_id = BindingId(4);
        let cond = NodeId(40);
        let body_expr = NodeId(41);
        let expr_id = NodeId(4);

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

        let module = make_single_binding_module(binding_id, expr_id, kinds);
        let ncx = NameContext::new();
        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let result = check_module(&module, options, &mut ty_ctx, &ncx);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn check_module_pattern_if_nilable_succeeds() {
        let binding_id = BindingId(5);
        let scrutinee = NodeId(50);
        let then_expr = NodeId(51);
        let else_expr = NodeId(52);
        let expr_id = NodeId(5);

        let mut kinds = HashMap::new();
        kinds.insert(scrutinee, ExprKind::Nil);
        kinds.insert(then_expr, ExprKind::LiteralBool(true));
        kinds.insert(else_expr, ExprKind::LiteralBool(false));
        kinds.insert(
            expr_id,
            ExprKind::IfPattern {
                scrutinee,
                pattern: Pattern::Some(binding_id),
                then_branch: then_expr,
                else_branch: Some(else_expr),
            },
        );

        let module = make_single_binding_module(binding_id, expr_id, kinds);
        let ncx = NameContext::new();
        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let result = check_module(&module, options, &mut ty_ctx, &ncx);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn check_module_loop_with_break_succeeds() {
        let binding_id = BindingId(6);
        let break_expr = NodeId(60);
        let loop_expr = NodeId(61);

        let mut kinds = HashMap::new();
        kinds.insert(break_expr, ExprKind::LiteralBool(true));
        kinds.insert(loop_expr, ExprKind::Loop { body: break_expr });

        let module = make_single_binding_module(binding_id, loop_expr, kinds);
        let ncx = NameContext::new();
        let global_env = GlobalEnv::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let options = TypecheckOptions::default();

        let result = check_module(&module, options, &mut ty_ctx, &ncx);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn check_module_struct_literal_with_hasfield_succeeds() {
        let binding_id = BindingId(2);
        let field_expr = NodeId(20);
        let expr_id = NodeId(2);

        let mut kinds = HashMap::new();
        kinds.insert(field_expr, ExprKind::LiteralBool(true));
        kinds.insert(
            expr_id,
            ExprKind::StructLiteral {
                struct_name: "A".to_string(),
                fields: vec![("x".to_string(), field_expr)],
            },
        );

        let module = make_single_binding_module(binding_id, expr_id, kinds);

        // Build a GlobalEnv with a struct A { x: bool } so HasField can succeed.
        let mut global_env = GlobalEnv::new();
        let struct_path = ray_shared::pathlib::Path::from("A");
        let bool_scheme = TyScheme::from_mono(Ty::bool());
        let struct_ty = crate::types::StructTy {
            kind: crate::types::NominalKind::Struct,
            path: struct_path.clone(),
            ty: TyScheme::from_mono(Ty::Const(struct_path.clone())),
            fields: vec![("x".to_string(), bool_scheme)],
        };
        global_env
            .structs
            .insert(struct_path.to_string(), struct_ty);

        let options = TypecheckOptions::default();
        let ncx = NameContext::new();
        let mut ty_ctx = TyCtx::new(global_env);
        let result = check_module(&module, options, &mut ty_ctx, &ncx);

        assert!(result.errors.is_empty());
    }

    #[test]
    fn solve_module_with_solve_bindings_basic_expression() {
        let binding_id = BindingId(1); // fn f(...)
        let root_expr = NodeId(10); // { 1u32 }
        let mut kinds = HashMap::new();
        kinds.insert(root_expr, ExprKind::LiteralIntSized(Ty::u32()));

        let mut subst = Subst::new();
        let global_env = GlobalEnv::new();
        let env = SolverEnv::default();
        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);

        let module = make_single_binding_module(binding_id, root_expr, kinds);

        let group = BindingGroup {
            bindings: vec![binding_id],
        };
        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| {
            println!("{}", item);
        });

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &[binding_id],
            &mut ctx,
            &env,
            &global_env,
            &mut subst,
            &mut errors,
        );

        println!("residuals: {:?}", residuals);
        println!("subst: {:?}", subst);
        println!("errors: {:?}", errors);
    }

    #[test]
    fn solve_module_with_solve_bindings_if_else() {
        let binding_id = BindingId(1); // fn f(...)
        let root_expr = NodeId(1); // if/else
        let cond = NodeId(2);
        let then_branch = NodeId(3);
        let else_branch = NodeId(4);
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
        let global_env = GlobalEnv::new();
        let env = SolverEnv::default();
        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);

        let module = make_single_binding_module(binding_id, root_expr, kinds);

        let group = BindingGroup {
            bindings: vec![binding_id],
        };
        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| {
            println!("{}", item);
        });

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &[binding_id],
            &mut ctx,
            &env,
            &global_env,
            &mut subst,
            &mut errors,
        );

        println!("errors: {:?}", errors);
        println!("residuals: {:?}", residuals);
        println!("subst: {}", subst);
    }

    fn make_multi_binding_module(
        binding_records: HashMap<BindingId, BindingRecord>,
        expr_kinds: HashMap<NodeId, ExprKind>,
    ) -> ModuleInput {
        let mut graph = BindingGraph::new();
        for bid in binding_records.keys() {
            graph.add_binding(*bid);
        }

        let expr_records = expr_kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        ModuleInput {
            bindings: graph,
            binding_records,
            node_bindings: HashMap::new(),
            expr_records,
            pattern_records: HashMap::new(),
            schema_allocator: Rc::new(RefCell::new(SchemaVarAllocator::new())),
            lowering_errors: Vec::new(),
        }
    }

    fn make_multi_binding_module_with_patterns(
        binding_records: HashMap<BindingId, BindingRecord>,
        expr_kinds: HashMap<NodeId, ExprKind>,
        pattern_records: HashMap<NodeId, PatternRecord>,
    ) -> ModuleInput {
        let mut graph = BindingGraph::new();
        for bid in binding_records.keys() {
            graph.add_binding(*bid);
        }

        let expr_records = expr_kinds
            .into_iter()
            .map(|(expr_id, kind)| (expr_id, ExprRecord { kind, source: None }))
            .collect();

        ModuleInput {
            bindings: graph,
            binding_records,
            node_bindings: HashMap::new(),
            expr_records,
            pattern_records,
            schema_allocator: Rc::new(RefCell::new(SchemaVarAllocator::new())),
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

        // Binding ids
        let main = BindingId(1);
        let id = BindingId(2); // local value binding inside main
        let x = BindingId(3); // closure parameter, nested under id
        let a = BindingId(4);
        let b = BindingId(5);

        // Expression node ids
        let main_root = NodeId(1000);
        let main_fn = NodeId(1004);

        // id = (x) => x
        let id_body = NodeId(100);
        let id_closure = NodeId(101);
        let assign_id = NodeId(1110);
        let pat_id = NodeId(1100);

        // a = id(1u32)
        let call_u32 = NodeId(1001);
        let callee_u32 = NodeId(1002);
        let arg_u32 = NodeId(1003);
        let assign_a = NodeId(1111);
        let pat_a = NodeId(1101);

        // b = id(true)
        let call_bool = NodeId(1011);
        let callee_bool = NodeId(1012);
        let arg_bool = NodeId(1013);
        let assign_b = NodeId(1112);
        let pat_b = NodeId(1102);

        // Build binding records.
        let mut binding_records: HashMap<BindingId, BindingRecord> = HashMap::new();

        // main is a top-level function binding.
        let mut main_rec = BindingRecord::new(BindingKind::Function { params: vec![] });
        main_rec.body_expr = Some(main_fn);
        binding_records.insert(main, main_rec);

        // id is a local value binding inside main.
        let mut id_rec = BindingRecord::new(BindingKind::Function { params: vec![x] });
        id_rec.parent = Some(main);
        id_rec.body_expr = Some(id_closure);
        binding_records.insert(id, id_rec);

        // x is a parameter binding for the closure; nest it under id.
        let mut x_rec = BindingRecord::new(BindingKind::Value);
        x_rec.parent = Some(id);
        binding_records.insert(x, x_rec);

        // locals a and b are also nested under main.
        let mut a_rec = BindingRecord::new(BindingKind::Value);
        a_rec.parent = Some(main);
        binding_records.insert(a, a_rec);

        let mut b_rec = BindingRecord::new(BindingKind::Value);
        b_rec.parent = Some(main);
        binding_records.insert(b, b_rec);

        // Build expression kinds.
        let mut kinds: HashMap<NodeId, ExprKind> = HashMap::new();

        // Closure body: just returns the param.
        kinds.insert(id_body, ExprKind::BindingRef(x));

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
        kinds.insert(callee_u32, ExprKind::BindingRef(id));
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
        kinds.insert(callee_bool, ExprKind::BindingRef(id));
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

        let module =
            make_multi_binding_module_with_patterns(binding_records, kinds, pattern_records);

        // Solve the top-level group containing only `main`. The local binding `id`
        // must be solved and generalized before its uses in later statements.
        let group = BindingGroup {
            bindings: vec![main],
        };

        let mut subst = Subst::new();
        let global_env = GlobalEnv::new();
        let env = SolverEnv::default();
        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);

        let mut root = build_constraint_tree_for_group(&module, &mut ctx, &group);
        walk_tree(&root, &mut |item| println!("{}", item));

        let mut errors = vec![];
        let residuals = solve_bindings(
            &module,
            &mut root,
            &group.bindings,
            &mut ctx,
            &env,
            &global_env,
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

        let malloc = BindingId(10);
        let main = BindingId(11);
        let malloc_arg = BindingId(12);

        let main_fn = NodeId(400);
        let main_root = NodeId(500);
        let malloc_callee = NodeId(501);
        let len_arg = NodeId(502);

        let malloc_scheme = TyScheme {
            vars: vec![],
            qualifiers: vec![],
            ty: Ty::func(vec![Ty::uint()], Ty::rawptr(Ty::u8())),
        };

        let int_trait_ty = TraitTy {
            path: Path::from("core::Int"),
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

        // Binding records
        let mut binding_records: HashMap<BindingId, BindingRecord> = HashMap::new();

        // malloc is a value binding with an annotated scheme.
        let mut malloc_rec = BindingRecord::new(BindingKind::Function {
            params: vec![malloc_arg],
        });
        malloc_rec.scheme = Some(malloc_scheme.clone());
        binding_records.insert(malloc, malloc_rec);

        // main is a top-level function binding.
        let mut main_rec = BindingRecord::new(BindingKind::Function { params: vec![] });
        main_rec.body_expr = Some(main_fn);
        binding_records.insert(main, main_rec);

        // Expressions
        let mut kinds: HashMap<NodeId, ExprKind> = HashMap::new();

        // fn main() { malloc(10) } where 10 is an unsized int literal that must be uint.
        kinds.insert(malloc_callee, ExprKind::BindingRef(malloc));
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

        let module = make_multi_binding_module(binding_records, kinds);
        let groups = vec![BindingGroup {
            bindings: vec![malloc, main],
        }];

        let mut global_env = GlobalEnv::new();
        global_env
            .traits
            .insert("core::Int".to_string(), int_trait_ty);
        global_env.add_impl(uint_int_impl);

        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);
        ctx.binding_schemes.insert(malloc, malloc_scheme);

        let result = solve_groups(&module, groups, &mut ctx, &global_env, None);
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
        //   x
        // }
        //
        // Here `10` is an unsized int literal with no contextual type.
        // We expect it to be resolved via defaulting from the `core::Int` trait.

        // Binding ids
        let main = BindingId(1);
        let x = BindingId(2);

        // Expression node ids
        let main_fn = NodeId(100);
        let main_root = NodeId(101);
        let assign_x = NodeId(102);
        let pat_x = NodeId(103);
        let lit_10 = NodeId(104);
        let var_x = NodeId(105);

        // Build binding records.
        let mut binding_records: HashMap<BindingId, BindingRecord> = HashMap::new();

        // main is a top-level function binding.
        let mut main_rec = BindingRecord::new(BindingKind::Function { params: vec![] });
        main_rec.body_expr = Some(main_fn);
        binding_records.insert(main, main_rec);

        // x is a local value binding inside main.
        let mut x_rec = BindingRecord::new(BindingKind::Value);
        x_rec.parent = Some(main);
        binding_records.insert(x, x_rec);

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

        // final expression is `x`
        kinds.insert(var_x, ExprKind::BindingRef(x));

        // Sequence the assignment and final value.
        kinds.insert(
            main_root,
            ExprKind::Sequence {
                items: vec![assign_x, var_x],
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

        let module =
            make_multi_binding_module_with_patterns(binding_records, kinds, pattern_records);

        // GlobalEnv: core::Int has a default type of `uint`, and there is an impl
        // Int[uint]. This should allow defaulting to pick `uint` for the literal.
        let mut global_env = GlobalEnv::new();

        let int_trait_ty = TraitTy {
            path: Path::from("core::Int"),
            ty: Ty::proj("core::Int", vec![Ty::var("'a")]),
            super_traits: vec![],
            fields: vec![],
            default_ty: Some(Ty::uint()),
        };
        global_env
            .traits
            .insert("core::Int".to_string(), int_trait_ty);

        let uint_int_impl = ImplTy {
            kind: ImplKind::Trait {
                base_ty: Ty::uint(),
                trait_ty: Ty::proj("core::Int", vec![Ty::uint()]),
                ty_args: vec![],
            },
            predicates: vec![],
            fields: vec![],
        };
        global_env.add_impl(uint_int_impl);

        // Solve only the top-level group containing `main`. Local bindings are
        // solved via binding nodes under `main`.
        let groups = vec![BindingGroup {
            bindings: vec![main],
        }];

        let ncx = NameContext::new();
        let mut ctx = SolverContext::new(Rc::default(), &ncx, &global_env);

        let result = solve_groups(&module, groups, &mut ctx, &global_env, None);
        assert!(
            result.errors.is_empty(),
            "expected no errors, got: {:?}",
            result.errors
        );

        // The literal should be defaulted to `uint`.
        let lit_ty = ctx
            .expr_types
            .get(&lit_10)
            .cloned()
            .unwrap_or_else(|| panic!("expected a type for literal node {:?}", lit_10));
        assert_eq!(lit_ty, Ty::uint());
    }
}
