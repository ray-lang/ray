//! Region validation for lifetime safety.
//!
//! Tracks the region (lifetime extent) of reference-typed values and ensures
//! that references do not outlive the data they point to. Each reference is
//! parameterized by a region that indicates how long the referenced data lives:
//!
//! - **Heap**: lives as long as the refcount > 0 (produced by `box`, `new`, `upgrade`)
//! - **Stack**: lives as long as the variable's stack frame (produced by `&x` / `&mut x`)
//! - **Call**: lives only for the duration of a function call (implicit reborrowing)
//! - **Destructor**: lives only for the destructor body
//! - **Param**: unknown until call site analysis (function parameters)

use std::collections::HashMap;

use ray_core::{
    ast::{BuiltinKind, Call, CurlyElement, Decl, Expr, FuncSig, Node, Pattern},
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::{DefId, DefKind},
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::FilePath,
    region::{OutlivesCause, OutlivesConstraint, RegionId, RegionInfo, RegionKind},
    resolution::DefTarget,
    span::Source,
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        bindings::local_binding_for_node,
        defs::{find_def_ast, func_def, impl_def},
        deps::region_call_group_for_def,
        libraries::library_data,
        resolve::name_resolutions,
        transform::file_ast,
        typecheck::{inferred_local_type, ty_of},
    },
    query::{Database, Query},
};

/// A constraint on a function parameter's region, discovered by analyzing
/// the function body. Checked at call sites against the argument's concrete region.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ParamConstraint {
    /// The parameter's region must outlive Heap (e.g., it is returned or
    /// stored in a heap-allocated struct).
    MustOutliveHeap { cause_expr: NodeId },
    /// The parameter's region must outlive another parameter's region
    /// (e.g., it is stored in a field of a struct pointed to by the other param).
    MustOutliveParam {
        other_param_index: usize,
        cause_expr: NodeId,
    },
}

/// Region requirements for a function: what constraints the function body
/// imposes on the regions of its reference-typed parameters.
/// Indexed by parameter position.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RegionRequirements {
    pub param_constraints: Vec<Vec<ParamConstraint>>,
}

/// Full result of region analysis: requirements (for callers to check)
/// plus errors (for diagnostics).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RegionAnalysis {
    pub requirements: RegionRequirements,
    pub errors: Vec<RayError>,
}

/// Analyze region constraints for a function definition.
///
/// Walks the function body, tracking regions of reference-typed values,
/// checking call sites against callees' requirements (transitively), and
/// collecting both outward-facing requirements (for this function's callers)
/// and errors (for diagnostics).
///
/// For library or primitive targets, returns empty analysis.
#[query]
pub fn analyze_regions(db: &Database, target: DefTarget) -> RegionAnalysis {
    let def_id = match target {
        DefTarget::Workspace(id) => id,
        DefTarget::Library(ref lib_def_id) => {
            let requirements = library_data(db, lib_def_id.module.clone())
                .and_then(|data| data.region_requirements.get(lib_def_id).cloned())
                .unwrap_or_default();
            return RegionAnalysis {
                requirements,
                errors: vec![],
            };
        }
        _ => return RegionAnalysis::default(),
    };

    let file_result = file_ast(db, def_id.file);
    let Some(def_header) = file_result.defs.iter().find(|h| h.def_id == def_id) else {
        return RegionAnalysis::default();
    };
    let Some(def_ast) = find_def_ast(&file_result.ast.decls, def_header.root_node) else {
        return RegionAnalysis::default();
    };

    let filepath = file_result.ast.filepath.clone();
    let mut ctx = RegionCtx::new(db, def_id, &filepath, &file_result.source_map);

    // Detect destructor methods: `destruct` inside `impl Destruct[...]`.
    ctx.is_destructor = matches!(def_header.kind, DefKind::Method)
        && def_header.name == "destruct"
        && def_header.parent.map_or(false, |parent_id| {
            impl_def(db, DefTarget::Workspace(parent_id))
                .as_ref()
                .as_ref()
                .map_or(false, |imp| {
                    imp.trait_ty
                        .as_ref()
                        .and_then(|ty| ty.item_path())
                        .and_then(|p| p.item_name())
                        == Some("Destruct")
                })
        });

    match &def_ast.value {
        Decl::Func(func) => {
            ctx.assign_param_regions(&func.sig);
            if let Some(body) = &func.body {
                let body_region = ctx.visit_expr(body);
                if let Some(region_id) = body_region {
                    ctx.add_return_constraint(region_id, body.id);
                }
            }
        }
        _ => {}
    }

    ctx.check_constraints();
    RegionAnalysis {
        requirements: RegionRequirements {
            param_constraints: ctx.param_constraints,
        },
        errors: ctx.errors,
    }
}

/// Context for region analysis within a single definition.
struct RegionCtx<'a> {
    db: &'a Database,
    def_id: DefId,
    #[allow(dead_code)]
    filepath: &'a FilePath,
    srcmap: &'a SourceMap,

    /// Maps local bindings to their current region.
    var_regions: HashMap<LocalBindingId, RegionId>,

    /// Maps expression nodes to their region (for lookup by later passes).
    expr_regions: HashMap<NodeId, RegionId>,

    /// All regions created during analysis.
    regions: Vec<RegionInfo>,

    /// Collected outlives constraints.
    constraints: Vec<OutlivesConstraint>,

    /// Requirements indexed by parameter position.
    /// Populated by both check_constraints (direct body constraints) and
    /// check_call_site (transitive propagation from callees).
    param_constraints: Vec<Vec<ParamConstraint>>,

    /// Maps LocalBindingId to param index for reference-typed parameters.
    local_id_to_param_index: HashMap<LocalBindingId, usize>,

    /// Total number of function parameters.
    num_params: usize,

    /// Whether this is a `destruct` method inside an `impl Destruct[...]`.
    is_destructor: bool,

    /// Counter for generating fresh RegionIds.
    next_id: u32,

    errors: Vec<RayError>,
}

impl<'a> RegionCtx<'a> {
    fn new(db: &'a Database, def_id: DefId, filepath: &'a FilePath, srcmap: &'a SourceMap) -> Self {
        Self {
            db,
            def_id,
            filepath,
            srcmap,
            var_regions: HashMap::new(),
            expr_regions: HashMap::new(),
            regions: Vec::new(),
            constraints: Vec::new(),
            param_constraints: Vec::new(),
            local_id_to_param_index: HashMap::new(),
            num_params: 0,
            is_destructor: false,
            next_id: 0,
            errors: Vec::new(),
        }
    }

    /// Create a fresh region with the given kind and provenance.
    fn fresh_region(
        &mut self,
        kind: RegionKind,
        origin_expr: NodeId,
        variable_name: Option<String>,
    ) -> RegionId {
        let id = RegionId(self.next_id);
        self.next_id += 1;
        self.regions.push(RegionInfo {
            kind,
            origin_expr,
            variable_name,
        });
        id
    }

    /// Add a constraint: src must outlive dest.
    fn add_constraint(&mut self, src: RegionId, dest: RegionId, cause: OutlivesCause) {
        self.constraints
            .push(OutlivesConstraint { src, dest, cause });
    }

    /// Add a return constraint: the returned region must outlive Heap.
    fn add_return_constraint(&mut self, region_id: RegionId, return_expr: NodeId) {
        let heap = self.fresh_region(RegionKind::Heap, return_expr, None);
        self.add_constraint(region_id, heap, OutlivesCause::Return { return_expr });
    }

    /// Check all collected constraints.
    ///
    /// For Param-sourced constraints that fail, records a `ParamConstraint`
    /// (checked at call sites instead of emitting an error here).
    /// For concrete region violations, emits errors directly.
    fn check_constraints(&mut self) {
        let mut errors = Vec::new();

        for constraint in &self.constraints {
            let src_info = &self.regions[constraint.src.0 as usize];
            let dest_info = &self.regions[constraint.dest.0 as usize];

            if src_info.kind.can_outlive(&dest_info.kind) {
                continue;
            }

            // Param-sourced constraints become requirements, not errors.
            if let RegionKind::Param(local_id) = &src_info.kind {
                if let Some(&param_idx) = self.local_id_to_param_index.get(local_id) {
                    let cause_expr = cause_node_id(&constraint.cause);
                    let pc = match &dest_info.kind {
                        RegionKind::Heap => ParamConstraint::MustOutliveHeap { cause_expr },
                        RegionKind::Param(other_id) => {
                            if let Some(&other_idx) = self.local_id_to_param_index.get(other_id) {
                                ParamConstraint::MustOutliveParam {
                                    other_param_index: other_idx,
                                    cause_expr,
                                }
                            } else {
                                continue;
                            }
                        }
                        _ => continue,
                    };
                    if param_idx < self.param_constraints.len() {
                        self.param_constraints[param_idx].push(pc);
                    }
                }
                continue;
            }

            errors.push(self.constraint_error(constraint, src_info));
        }

        self.errors.extend(errors);
    }

    /// Generate an error message for a failed constraint.
    fn constraint_error(&self, constraint: &OutlivesConstraint, src_info: &RegionInfo) -> RayError {
        let msg = match &constraint.cause {
            OutlivesCause::Return { .. } => {
                let var_name = src_info.variable_name.as_deref().unwrap_or("value");
                match &src_info.kind {
                    RegionKind::Stack(_) => format!(
                        "cannot return a reference to local variable `{}` — \
                         it does not live long enough",
                        var_name
                    ),
                    RegionKind::Call(_) | RegionKind::Param(_) => {
                        "cannot return a borrowed reference — \
                         the reference is only valid for the duration of the call"
                            .to_string()
                    }
                    RegionKind::Destructor => "cannot return `*mut self` from a destructor — \
                         the reference is only valid for the destructor body"
                        .to_string(),
                    _ => "cannot return reference — it does not live long enough".to_string(),
                }
            }
            OutlivesCause::StoreInField { field_name, .. } => {
                let var_name = src_info.variable_name.as_deref().unwrap_or("value");
                format!(
                    "cannot store reference to `{}` in field `{}` — \
                     it does not live long enough",
                    var_name, field_name
                )
            }
            OutlivesCause::Assignment { .. } => {
                "cannot assign reference — it does not live long enough".to_string()
            }
        };

        let src_locations: Vec<Source> = match &constraint.cause {
            OutlivesCause::Return { return_expr } => {
                self.srcmap.get_by_id(*return_expr).into_iter().collect()
            }
            OutlivesCause::StoreInField { struct_expr, .. } => {
                self.srcmap.get_by_id(*struct_expr).into_iter().collect()
            }
            OutlivesCause::Assignment { assign_expr } => {
                self.srcmap.get_by_id(*assign_expr).into_iter().collect()
            }
        };

        RayError {
            msg,
            src: src_locations,
            kind: RayErrorKind::Type,
            context: Some("region validation".to_string()),
        }
    }

    /// Assign regions to reference-typed function parameters.
    ///
    /// - `move` parameters get Heap regions (they own the reference).
    /// - Non-move reference parameters get Param regions (unknown until call site).
    /// - Value-type parameters are skipped.
    ///
    /// Also builds the `local_id_to_param_index` mapping and initializes
    /// `param_constraints` with the correct size.
    fn assign_param_regions(&mut self, sig: &FuncSig) {
        self.num_params = sig.params.len();
        self.param_constraints = vec![Vec::new(); self.num_params];

        for (idx, param) in sig.params.iter().enumerate() {
            let Some(local_id) = local_binding_for_node(self.db, param.id) else {
                continue;
            };
            let Some(ty) = inferred_local_type(self.db, local_id) else {
                continue;
            };
            if !(ty.is_shared_ref() || ty.is_mut_ref() || ty.is_id_ref()) {
                continue;
            }

            self.local_id_to_param_index.insert(local_id, idx);

            let param_name = param.value.name().to_short_name();
            let region = if param.value.is_move() {
                self.fresh_region(RegionKind::Heap, param.id, Some(param_name))
            } else if self.is_destructor && param_name == "self" {
                self.fresh_region(RegionKind::Destructor, param.id, Some(param_name))
            } else {
                self.fresh_region(RegionKind::Param(local_id), param.id, Some(param_name))
            };
            self.var_regions.insert(local_id, region);
        }
    }

    /// Check a call site against the callee's region requirements.
    ///
    /// Resolves the callee, looks up its region requirements (transitively
    /// via `analyze_regions`), then verifies that each argument's concrete
    /// region satisfies the callee's constraints. For arguments with Param
    /// regions, propagates the constraint to this function's own requirements.
    fn check_call_site(&mut self, call: &Call) {
        // Resolve callee to DefTarget.
        let callee_id = call.call_resolution_id();
        let resolutions = name_resolutions(self.db, self.def_id.file);
        let Some(target) = resolutions.get(&callee_id).and_then(|r| r.to_def_target()) else {
            return;
        };

        // Get the callee's region requirements, handling same-group cycles.
        let callee_requirements = match &target {
            DefTarget::Workspace(callee_def_id) => {
                let same_group = region_call_group_for_def(self.db, self.def_id)
                    .and_then(|my_group| {
                        region_call_group_for_def(self.db, *callee_def_id)
                            .map(|their_group| my_group == their_group)
                    })
                    .unwrap_or(false);

                if same_group {
                    // Conservative: assume all params must outlive Heap to break cycle.
                    let num_params = func_def(self.db, target.clone())
                        .map(|fd| fd.params.len())
                        .unwrap_or(0);
                    RegionRequirements {
                        param_constraints: (0..num_params)
                            .map(|_| {
                                vec![ParamConstraint::MustOutliveHeap {
                                    cause_expr: call.callee.id,
                                }]
                            })
                            .collect(),
                    }
                } else {
                    analyze_regions(self.db, target.clone()).requirements
                }
            }
            _ => analyze_regions(self.db, target.clone()).requirements,
        };

        if callee_requirements
            .param_constraints
            .iter()
            .all(|c| c.is_empty())
        {
            return;
        }

        // Build full argument list including self for method calls.
        let mut arg_regions: Vec<Option<RegionId>> = Vec::new();
        if call.is_method_call() {
            if let Expr::Dot(dot) = &call.callee.value {
                arg_regions.push(self.expr_regions.get(&dot.lhs.id).copied());
            }
        }
        for arg in &call.args.items {
            arg_regions.push(self.expr_regions.get(&arg.id).copied());
        }

        // Check each param's constraints against the argument's region.
        for (param_idx, constraints) in callee_requirements.param_constraints.iter().enumerate() {
            let Some(Some(arg_region)) = arg_regions.get(param_idx) else {
                continue;
            };
            let arg_info = &self.regions[arg_region.0 as usize];

            for constraint in constraints {
                match constraint {
                    ParamConstraint::MustOutliveHeap { .. } => {
                        if let RegionKind::Param(local_id) = &arg_info.kind {
                            // Transitive propagation: callee requires Heap,
                            // our argument is a Param — propagate to our requirements.
                            if let Some(&our_idx) = self.local_id_to_param_index.get(local_id) {
                                self.param_constraints[our_idx].push(
                                    ParamConstraint::MustOutliveHeap {
                                        cause_expr: call.callee.id,
                                    },
                                );
                            }
                        } else if !arg_info.kind.can_outlive(&RegionKind::Heap) {
                            let var_name = arg_info.variable_name.as_deref().unwrap_or("argument");
                            self.errors.push(RayError {
                                msg: format!(
                                    "cannot pass `{var_name}` — the callee requires \
                                     this reference to outlive the call, but it does \
                                     not live long enough"
                                ),
                                src: self.srcmap.get_by_id(call.callee.id).into_iter().collect(),
                                kind: RayErrorKind::Type,
                                context: Some("region validation".to_string()),
                            });
                        }
                    }
                    ParamConstraint::MustOutliveParam {
                        other_param_index, ..
                    } => {
                        let other_region = arg_regions.get(*other_param_index).and_then(|r| *r);
                        let Some(other_region) = other_region else {
                            continue;
                        };
                        let other_info = &self.regions[other_region.0 as usize];

                        match (&arg_info.kind, &other_info.kind) {
                            // Both are Param — propagate param-to-param constraint.
                            (RegionKind::Param(src_local), RegionKind::Param(dest_local)) => {
                                if let (Some(&src_idx), Some(&dest_idx)) = (
                                    self.local_id_to_param_index.get(src_local),
                                    self.local_id_to_param_index.get(dest_local),
                                ) {
                                    self.param_constraints[src_idx].push(
                                        ParamConstraint::MustOutliveParam {
                                            other_param_index: dest_idx,
                                            cause_expr: call.callee.id,
                                        },
                                    );
                                }
                            }
                            // Our param must outlive a concrete Heap region.
                            (RegionKind::Param(src_local), RegionKind::Heap) => {
                                if let Some(&src_idx) = self.local_id_to_param_index.get(src_local)
                                {
                                    self.param_constraints[src_idx].push(
                                        ParamConstraint::MustOutliveHeap {
                                            cause_expr: call.callee.id,
                                        },
                                    );
                                }
                            }
                            // Our param must outlive a non-Heap concrete region.
                            // This is inherently satisfied: the caller's reference
                            // lives at least as long as the call, which outlives
                            // any local/call-scoped region in our body.
                            (RegionKind::Param(_), _) => {}
                            // Concrete regions — check directly.
                            _ => {
                                if !arg_info.kind.can_outlive(&other_info.kind) {
                                    let var_name =
                                        arg_info.variable_name.as_deref().unwrap_or("argument");
                                    let other_name = func_def(self.db, target.clone())
                                        .and_then(|fd| {
                                            fd.params
                                                .get(*other_param_index)
                                                .map(|p| p.name.clone())
                                        })
                                        .unwrap_or_else(|| "parameter".to_string());
                                    self.errors.push(RayError {
                                        msg: format!(
                                            "cannot pass `{var_name}` — it must live at \
                                             least as long as `{other_name}`, but it \
                                             does not live long enough"
                                        ),
                                        src: self
                                            .srcmap
                                            .get_by_id(call.callee.id)
                                            .into_iter()
                                            .collect(),
                                        kind: RayErrorKind::Type,
                                        context: Some("region validation".to_string()),
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Recursively visit an expression, tracking regions of reference-typed values.
    ///
    /// Returns the region of the expression if it produces a reference-typed value.
    fn visit_expr(&mut self, expr: &Node<Expr>) -> Option<RegionId> {
        let region = match &expr.value {
            Expr::Block(block) => {
                let mut last_region = None;
                for stmt in &block.stmts {
                    last_region = self.visit_expr(stmt);
                }
                last_region
            }

            Expr::Assign(assign) => {
                let rhs_region = self.visit_expr(&assign.rhs);
                // If the LHS is a simple name binding and the RHS has a region,
                // track the variable's region.
                if let Some(region_id) = rhs_region {
                    if let Pattern::Name(_) = &assign.lhs.value {
                        if let Some(local_id) = local_binding_for_node(self.db, assign.lhs.id) {
                            self.var_regions.insert(local_id, region_id);
                        }
                    }
                }
                None
            }

            Expr::Boxed(boxed) => {
                self.visit_expr(&boxed.inner);
                Some(self.fresh_region(RegionKind::Heap, expr.id, None))
            }

            Expr::New(_) => Some(self.fresh_region(RegionKind::Heap, expr.id, None)),

            Expr::BuiltinCall(bc) => match bc.kind {
                BuiltinKind::Freeze | BuiltinKind::Id => self.visit_expr(&bc.arg),
                BuiltinKind::Upgrade => {
                    self.visit_expr(&bc.arg);
                    Some(self.fresh_region(RegionKind::Heap, expr.id, None))
                }
            },

            Expr::Name(_) => local_binding_for_node(self.db, expr.id)
                .and_then(|local_id| self.var_regions.get(&local_id).copied()),

            Expr::Return(ret) => {
                let ret_region = ret.as_ref().and_then(|val| self.visit_expr(val));
                if let Some(region_id) = ret_region {
                    self.add_return_constraint(region_id, expr.id);
                }
                None
            }

            Expr::If(if_expr) => {
                self.visit_expr(&if_expr.cond);
                let then_region = self.visit_expr(&if_expr.then);
                let else_region = if_expr.els.as_ref().and_then(|e| self.visit_expr(e));
                then_region.or(else_region)
            }

            Expr::Call(call) => {
                self.visit_expr(&call.callee);
                for arg in &call.args.items {
                    self.visit_expr(arg);
                }
                self.check_call_site(call);
                // If the call returns a reference type, assign Heap region.
                // Callee validation ensures returned references outlive Heap.
                let result_is_ref = ty_of(self.db, expr.id)
                    .map(|ty| ty.is_shared_ref() || ty.is_mut_ref() || ty.is_id_ref())
                    .unwrap_or(false);
                if result_is_ref {
                    Some(self.fresh_region(RegionKind::Heap, expr.id, None))
                } else {
                    None
                }
            }

            Expr::Dot(dot) => {
                let lhs_region = self.visit_expr(&dot.lhs);
                // Propagate region only if the dot result is a reference type.
                let result_is_ref = ty_of(self.db, expr.id)
                    .map(|ty| ty.is_shared_ref() || ty.is_mut_ref() || ty.is_id_ref())
                    .unwrap_or(false);
                if result_is_ref { lhs_region } else { None }
            }

            Expr::BinOp(binop) => {
                self.visit_expr(&binop.lhs);
                self.visit_expr(&binop.rhs);
                None
            }

            Expr::UnaryOp(unop) => {
                self.visit_expr(&unop.expr);
                None
            }

            Expr::Sequence(seq) => {
                let mut last = None;
                for item in &seq.items {
                    last = self.visit_expr(item);
                }
                last
            }

            Expr::Tuple(tup) => {
                for item in &tup.seq.items {
                    self.visit_expr(item);
                }
                None
            }

            Expr::For(for_expr) => {
                self.visit_expr(&for_expr.expr);
                self.visit_expr(&for_expr.body);
                None
            }

            Expr::While(while_expr) => {
                self.visit_expr(&while_expr.cond);
                self.visit_expr(&while_expr.body);
                None
            }

            Expr::Loop(loop_expr) => {
                self.visit_expr(&loop_expr.body);
                None
            }

            Expr::Index(index) => {
                self.visit_expr(&index.lhs);
                self.visit_expr(&index.index);
                None
            }

            Expr::Ref(rf) => {
                self.visit_expr(&rf.expr);
                // Determine the variable being referenced for stack region tracking.
                let local_id = local_binding_for_node(self.db, rf.expr.id);
                if let Some(local_id) = local_id {
                    let var_name = rf.expr.value.get_name();
                    Some(self.fresh_region(RegionKind::Stack(local_id), expr.id, var_name))
                } else {
                    // Complex expression (field access, etc.) — propagate inner region.
                    self.expr_regions.get(&rf.expr.id).copied()
                }
            }

            Expr::Deref(deref) => {
                self.visit_expr(&deref.expr);
                None
            }

            Expr::Curly(curly) => {
                for elem in &curly.elements {
                    match &elem.value {
                        CurlyElement::Labeled(_, val) => {
                            self.visit_expr(val);
                        }
                        CurlyElement::Name(_) => {}
                    }
                }
                None
            }

            Expr::List(list) => {
                for item in &list.items {
                    self.visit_expr(item);
                }
                None
            }

            Expr::Closure(closure) => {
                self.visit_expr(&closure.body);
                None
            }

            Expr::Cast(cast) => {
                self.visit_expr(&cast.lhs);
                None
            }

            Expr::ScopedAccess(sa) => {
                self.visit_expr(&sa.lhs);
                None
            }

            // Literals and other leaf expressions — no sub-expressions to visit.
            _ => None,
        };

        // Cache the region for this expression node.
        if let Some(region_id) = region {
            self.expr_regions.insert(expr.id, region_id);
        }

        region
    }
}

/// Extract the originating NodeId from an outlives cause.
fn cause_node_id(cause: &OutlivesCause) -> NodeId {
    match cause {
        OutlivesCause::Return { return_expr } => *return_expr,
        OutlivesCause::StoreInField { struct_expr, .. } => *struct_expr,
        OutlivesCause::Assignment { assign_expr } => *assign_expr,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_core::errors::RayError;
    use ray_shared::{
        def::DefKind,
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
        resolution::DefTarget,
    };

    use crate::{
        queries::{
            libraries::LoadedLibraries,
            parse::parse_file,
            regions::{ParamConstraint, RegionAnalysis, analyze_regions},
            workspace::{CompilerOptions, FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    fn setup_test_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.to_path());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        db.set_input::<CompilerOptions>(
            (),
            CompilerOptions {
                no_core: true,
                test_mode: false,
            },
        );
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(
            &db,
            file_id,
            FilePath::from("test/mod.ray"),
            module_path.clone(),
        );
        (db, file_id)
    }

    fn find_def_errors(source: &str, fn_name: &str) -> Vec<RayError> {
        find_def_analysis(source, fn_name).errors
    }

    fn find_def_analysis(source: &str, fn_name: &str) -> RegionAnalysis {
        let (db, file_id) = setup_test_db(source);
        let parse_result = parse_file(&db, file_id);
        let def = parse_result
            .defs
            .iter()
            .find(|d| d.name == fn_name)
            .unwrap_or_else(|| panic!("should find function `{}`", fn_name));
        analyze_regions(&db, DefTarget::Workspace(def.def_id))
    }

    /// Find errors for an impl method (filters for methods whose parent
    /// is an Impl, to avoid matching the trait signature with the same name).
    fn find_method_errors(source: &str, method_name: &str) -> Vec<RayError> {
        let (db, file_id) = setup_test_db(source);
        let parse_result = parse_file(&db, file_id);
        let def = parse_result
            .defs
            .iter()
            .find(|d| {
                d.name == method_name
                    && matches!(d.kind, DefKind::Method)
                    && d.parent.map_or(false, |pid| {
                        parse_result
                            .defs
                            .iter()
                            .any(|p| p.def_id == pid && matches!(p.kind, DefKind::Impl))
                    })
            })
            .unwrap_or_else(|| panic!("should find impl method `{}`", method_name));
        analyze_regions(&db, DefTarget::Workspace(def.def_id)).errors
    }

    #[test]
    fn heap_box_returned_no_error() {
        let errors = find_def_errors(
            r#"
fn foo() {
    p = box(42)
    p
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Returning a boxed value should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn heap_freeze_returned_no_error() {
        let errors = find_def_errors(
            r#"
fn foo() {
    p = box(42)
    freeze(p)
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Returning freeze of a boxed value should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn heap_freeze_via_variable_no_error() {
        let errors = find_def_errors(
            r#"
fn foo() {
    p = box(42)
    q = freeze(p)
    q
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Returning frozen ref via variable should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn heap_id_returned_no_error() {
        let errors = find_def_errors(
            r#"
fn foo() {
    p = box(42)
    q = freeze(p)
    id(q)
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Returning id ref of frozen box should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn no_regions_for_value_types() {
        let errors = find_def_errors(
            r#"
fn foo() {
    x = 42
    x
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Value-type code should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn explicit_return_heap_no_error() {
        let errors = find_def_errors(
            r#"
fn foo() {
    p = box(42)
    return p
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Explicit return of boxed value should produce no region errors, got: {:?}",
            errors
        );
    }

    #[test]
    fn heap_through_if_branches_no_error() {
        let errors = find_def_errors(
            r#"
fn foo(cond: bool) {
    if cond { box(1) } else { box(2) }
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Heap refs through if branches should produce no region errors, got: {:?}",
            errors
        );
    }

    // ---- Parameter region tests ----

    #[test]
    fn value_param_no_region_requirements() {
        let analysis = find_def_analysis(
            r#"
struct S {}
fn value_fn(x: S) -> S => x
"#,
            "value_fn",
        );
        assert!(
            analysis.errors.is_empty(),
            "Value-type function should produce no errors: {:?}",
            analysis.errors
        );
        assert!(
            analysis
                .requirements
                .param_constraints
                .iter()
                .all(|c| c.is_empty()),
            "Value-type param should have no region requirements: {:?}",
            analysis.requirements
        );
    }

    #[test]
    fn ref_param_not_returned_no_requirements() {
        let analysis = find_def_analysis(
            r#"
struct S {}
struct R {}
fn use_ref(x: *S) -> R => R {}
"#,
            "use_ref",
        );
        assert!(
            analysis.errors.is_empty(),
            "Ref param not returned should produce no errors: {:?}",
            analysis.errors
        );
        assert!(
            analysis
                .requirements
                .param_constraints
                .iter()
                .all(|c| c.is_empty()),
            "Unused ref param should have no requirements: {:?}",
            analysis.requirements
        );
    }

    #[test]
    fn ref_param_returned_requires_heap() {
        let analysis = find_def_analysis(
            r#"
struct S {}
fn returns_ref(x: *S) -> *S => x
"#,
            "returns_ref",
        );
        assert!(
            analysis.errors.is_empty(),
            "Returning param ref should not error in the callee: {:?}",
            analysis.errors
        );
        assert!(
            !analysis.requirements.param_constraints.is_empty(),
            "Should have param constraints"
        );
        assert!(
            analysis.requirements.param_constraints[0]
                .iter()
                .any(|c| matches!(c, ParamConstraint::MustOutliveHeap { .. })),
            "Returned ref param should require MustOutliveHeap: {:?}",
            analysis.requirements
        );
    }

    #[test]
    fn move_ref_param_returned_no_requirements() {
        let analysis = find_def_analysis(
            r#"
struct S {}
fn returns_move(move x: *mut S) -> *mut S => x
"#,
            "returns_move",
        );
        assert!(
            analysis.errors.is_empty(),
            "Move param returned should produce no errors: {:?}",
            analysis.errors
        );
        assert!(
            analysis
                .requirements
                .param_constraints
                .iter()
                .all(|c| c.is_empty()),
            "Move ref param should have no requirements (Heap region): {:?}",
            analysis.requirements
        );
    }

    #[test]
    fn call_with_heap_arg_satisfies_heap_requirement() {
        let errors = find_def_errors(
            r#"
struct S {}
fn returns_ref(x: *S) -> *S => x

fn caller() {
    p = box(S {})
    returns_ref(freeze(p))
}
"#,
            "caller",
        );
        assert!(
            errors.is_empty(),
            "Calling with Heap arg should satisfy MustOutliveHeap: {:?}",
            errors
        );
    }

    #[test]
    fn transitive_propagation_through_call_chain() {
        let source = r#"
struct S {}
fn inner(x: *S) -> *S => x

fn outer(y: *S) -> *S => inner(y)
"#;
        // inner requires param 0 to outlive Heap (returns it).
        let inner_analysis = find_def_analysis(source, "inner");
        assert!(
            inner_analysis.requirements.param_constraints[0]
                .iter()
                .any(|c| matches!(c, ParamConstraint::MustOutliveHeap { .. })),
            "inner should require param 0 MustOutliveHeap"
        );

        // outer should transitively get the same requirement.
        let outer_analysis = find_def_analysis(source, "outer");
        assert!(
            outer_analysis.errors.is_empty(),
            "outer should have no errors: {:?}",
            outer_analysis.errors
        );
        assert!(
            outer_analysis.requirements.param_constraints[0]
                .iter()
                .any(|c| matches!(c, ParamConstraint::MustOutliveHeap { .. })),
            "outer should transitively require param 0 MustOutliveHeap: {:?}",
            outer_analysis.requirements
        );
    }

    #[test]
    fn same_group_conservative_requirements() {
        let source = r#"
struct S {}
fn ping(x: *S) -> *S => pong(x)
fn pong(x: *S) -> *S => ping(x)
"#;
        // Mutual recursion: same binding group → conservative MustOutliveHeap.
        let ping_analysis = find_def_analysis(source, "ping");
        assert!(
            ping_analysis.errors.is_empty(),
            "ping should have no errors: {:?}",
            ping_analysis.errors
        );
        assert!(
            ping_analysis.requirements.param_constraints[0]
                .iter()
                .any(|c| matches!(c, ParamConstraint::MustOutliveHeap { .. })),
            "ping should conservatively require param 0 MustOutliveHeap: {:?}",
            ping_analysis.requirements
        );
    }

    #[test]
    fn no_requirements_when_callee_has_none() {
        let source = r#"
struct S {}
struct R {}
fn noop(x: *S) -> R => R {}

fn caller(y: *S) {
    noop(y)
}
"#;
        let analysis = find_def_analysis(source, "caller");
        assert!(
            analysis.errors.is_empty(),
            "caller should have no errors: {:?}",
            analysis.errors
        );
        assert!(
            analysis
                .requirements
                .param_constraints
                .iter()
                .all(|c| c.is_empty()),
            "caller should have no requirements when callee has none: {:?}",
            analysis.requirements
        );
    }

    // ---- Stack region tests ----

    #[test]
    fn stack_ref_used_locally_no_error() {
        let errors = find_def_errors(
            r#"
struct S {}
fn foo() {
    x = S {}
    p = &x
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Stack ref used locally should produce no errors: {:?}",
            errors
        );
    }

    #[test]
    fn stack_ref_returned_error() {
        let errors = find_def_errors(
            r#"
struct S {}
fn foo() {
    x = S {}
    &x
}
"#,
            "foo",
        );
        assert!(
            !errors.is_empty(),
            "Returning a stack ref should produce a region error"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot return") && e.msg.contains("x")),
            "Error should mention returning local variable: {:?}",
            errors
        );
    }

    #[test]
    fn stack_mut_ref_returned_error() {
        let errors = find_def_errors(
            r#"
struct S {}
fn foo() {
    mut x = S {}
    &mut x
}
"#,
            "foo",
        );
        assert!(
            !errors.is_empty(),
            "Returning a mutable stack ref should produce a region error"
        );
        assert!(
            errors
                .iter()
                .any(|e| e.msg.contains("cannot return") && e.msg.contains("x")),
            "Error should mention returning local variable: {:?}",
            errors
        );
    }

    #[test]
    fn stack_ref_assigned_to_var_then_returned_error() {
        let errors = find_def_errors(
            r#"
struct S {}
fn foo() {
    x = S {}
    p = &x
    p
}
"#,
            "foo",
        );
        assert!(
            !errors.is_empty(),
            "Returning stack ref via variable should produce a region error"
        );
    }

    #[test]
    fn stack_ref_passed_to_escaping_callee_error() {
        let errors = find_def_errors(
            r#"
struct S {}
fn returns_ref(r: *S) -> *S => r

fn foo() {
    x = S {}
    returns_ref(&x)
}
"#,
            "foo",
        );
        assert!(
            !errors.is_empty(),
            "Passing stack ref to function that returns it should produce an error"
        );
    }

    #[test]
    fn stack_ref_passed_to_non_escaping_callee_no_error() {
        let errors = find_def_errors(
            r#"
struct S {}
struct R {}
fn use_ref(r: *S) -> R => R {}

fn foo() {
    x = S {}
    use_ref(&x)
}
"#,
            "foo",
        );
        assert!(
            errors.is_empty(),
            "Passing stack ref to non-escaping function should be OK: {:?}",
            errors
        );
    }

    // ---- Destructor region tests ----

    #[test]
    fn destructor_self_used_locally_no_error() {
        let source = r#"
struct Res { val: int }

trait Destruct['a] {
    fn destruct(self: *mut 'a)
}

impl Destruct[Res] {
    fn destruct(self: *mut Res) {
        x = self.val
    }
}
"#;
        let errors = find_method_errors(source, "destruct");
        assert!(
            errors.is_empty(),
            "Destructor using self locally should produce no errors: {:?}",
            errors
        );
    }

    #[test]
    fn destructor_self_returned_error() {
        let source = r#"
struct Res { val: int }

trait Destruct['a] {
    fn destruct(self: *mut 'a)
}

impl Destruct[Res] {
    fn destruct(self: *mut Res) -> *mut Res => self
}
"#;
        let errors = find_method_errors(source, "destruct");
        assert!(
            !errors.is_empty(),
            "Returning *mut self from destructor should produce a region error"
        );
        assert!(
            errors.iter().any(|e| e.msg.contains("destructor")),
            "Error should mention destructor: {:?}",
            errors
        );
    }
}
