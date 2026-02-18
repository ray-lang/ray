//! Inlay hints query for LSP inline annotations.
//!
//! Produces a list of inlay hints for a file by walking the raw AST.
//! Two kinds of hints are generated:
//!
//! 1. **Type hints** (`: TYPE`) — shown after unannotated bindings,
//!    closure parameters, and intermediate calls in multi-line dot chains.
//!
//! 2. **Parameter name hints** (`param: `) — shown before function call
//!    arguments, skipped when the argument name already matches.

use std::collections::HashMap;
use std::sync::Arc;

use ray_core::ast::{Call, Closure, Expr, InfixOp, Node, Pattern, WalkItem, walk_file};
use ray_query_macros::query;
use ray_shared::{
    file_id::FileId,
    node_id::NodeId,
    resolution::{DefTarget, Resolution},
    span::Span,
};
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        calls::call_resolution, defs::func_def, display::display_ty, locations, parse::parse_file,
        resolve::name_resolutions, symbols::call_site_index, typecheck::ty_of,
    },
    query::{Database, Query},
};

/// A single inlay hint produced by the query.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InlayHintData {
    /// The span whose start or end determines hint placement.
    pub span: Span,
    /// What kind of hint this is.
    pub kind: InlayHintDataKind,
}

/// The kind of inlay hint.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum InlayHintDataKind {
    /// `: TYPE` shown after a binding or expression.
    Type(String),
    /// `param_name: ` shown before a function argument.
    Parameter(String),
}

/// Produces inlay hints for a file.
///
/// Walks the raw (untransformed) AST to ensure accurate source spans.
/// Calls `ty_of` on the same node IDs — most expression nodes preserve
/// their IDs through transformation, and `ty_of` returns `None` for
/// any synthetic nodes (which we skip).
#[query]
pub fn inlay_hints(db: &Database, file_id: FileId) -> Arc<Vec<InlayHintData>> {
    let parse_result = parse_file(db, file_id);
    let resolutions = name_resolutions(db, file_id);
    let call_sites = call_site_index(db, file_id);
    let mut hints = Vec::new();

    for item in walk_file(&parse_result.ast) {
        let WalkItem::Expr(expr) = item else {
            continue;
        };

        match &expr.value {
            Expr::Assign(assign) => {
                // Type hints on unannotated bindings
                if matches!(assign.op, InfixOp::Assign) {
                    collect_pattern_type_hints(db, &assign.lhs, &mut hints);
                }
            }
            Expr::Closure(closure) => {
                collect_closure_param_hints(db, closure, &mut hints);
            }
            Expr::Call(call) => {
                // Multi-line dot chain: emit hint for the LHS (receiver) of the dot
                collect_dot_chain_hints(db, call, &mut hints);

                // Parameter name hints
                collect_param_name_hints(db, call, &resolutions, &call_sites, &mut hints);
            }
            _ => {}
        }
    }

    Arc::new(hints)
}

/// Recursively collect type hints for unannotated names in a pattern.
fn collect_pattern_type_hints(
    db: &Database,
    pattern: &Node<Pattern>,
    hints: &mut Vec<InlayHintData>,
) {
    match &pattern.value {
        Pattern::Name(name) => {
            if name.ty.is_none() {
                if let Some(ty) = ty_of(db, pattern.id) {
                    let displayed = display_ty(db, pattern.id.owner, &ty);
                    if let Some(span) = locations::span_of(db, pattern.id) {
                        hints.push(InlayHintData {
                            span,
                            kind: InlayHintDataKind::Type(displayed.to_string()),
                        });
                    }
                }
            }
        }
        Pattern::Tuple(pats) | Pattern::Sequence(pats) => {
            for pat in pats {
                collect_pattern_type_hints(db, pat, hints);
            }
        }
        Pattern::Some(inner) => {
            collect_pattern_type_hints(db, inner, hints);
        }
        _ => {}
    }
}

/// Collect type hints for unannotated closure parameters.
fn collect_closure_param_hints(db: &Database, closure: &Closure, hints: &mut Vec<InlayHintData>) {
    for arg in &closure.args.items {
        // Closure parameters are expressions; check if they're simple names
        if let Expr::Name(name) = &arg.value {
            if name.ty.is_none() {
                if let Some(ty) = ty_of(db, arg.id) {
                    let displayed = display_ty(db, arg.id.owner, &ty);
                    if let Some(span) = locations::span_of(db, arg.id) {
                        hints.push(InlayHintData {
                            span,
                            kind: InlayHintDataKind::Type(displayed.to_string()),
                        });
                    }
                }
            }
        }
    }
}

/// Emit type hints for intermediate calls in a multi-line dot chain.
///
/// For a chain like:
/// ```text
/// result = self.documents
///               .get(10)
///               .map(...)
/// ```
/// We emit hints for `self.documents` and `.get(10)` but NOT `.map(...)`.
///
/// We do this by looking at the LHS of the dot: if the dot starts on a
/// different line than the LHS ends, it's a multi-line step, and we emit
/// a type hint for the LHS.
fn collect_dot_chain_hints(db: &Database, call: &Call, hints: &mut Vec<InlayHintData>) {
    let Expr::Dot(dot) = &call.callee.value else {
        return;
    };

    // Get the end position of the LHS expression.
    // For calls, use paren_span (ends after closing paren).
    // For other expressions, use span_of from the source map.
    let lhs_end_span = match &dot.lhs.value {
        Expr::Call(inner_call) => Some(inner_call.paren_span),
        _ => locations::span_of(db, dot.lhs.id),
    };

    let Some(lhs_span) = lhs_end_span else {
        return;
    };

    if lhs_span.end.lineno >= dot.dot.span.start.lineno {
        // Same line — not a multi-line chain
        return;
    }

    // Emit type hint for the LHS (the receiver/intermediate expression)
    if let Some(ty) = ty_of(db, dot.lhs.id) {
        let displayed = display_ty(db, dot.lhs.id.owner, &ty);
        hints.push(InlayHintData {
            span: lhs_span,
            kind: InlayHintDataKind::Type(displayed.to_string()),
        });
    }
}

/// Collect parameter name hints for a function call.
fn collect_param_name_hints(
    db: &Database,
    call: &Call,
    resolutions: &HashMap<NodeId, Resolution>,
    call_sites: &HashMap<NodeId, NodeId>,
    hints: &mut Vec<InlayHintData>,
) {
    if call.args.items.is_empty() {
        return;
    }

    // Resolve the callee to a DefTarget
    let target = resolve_call_target(db, call, resolutions, call_sites);
    let Some(target) = target else {
        return;
    };

    // Get param names from the function definition
    let Some(func) = func_def(db, target) else {
        return;
    };

    // Method calls (dot syntax) have an implicit self parameter
    let is_method = matches!(call.callee.value, Expr::Dot(_));
    let param_offset = if is_method { 1 } else { 0 };

    for (i, arg) in call.args.items.iter().enumerate() {
        let param_idx = i + param_offset;
        let Some(param) = func.params.get(param_idx) else {
            continue;
        };

        // Skip if argument is a variable whose name matches the parameter
        if arg_name_matches(arg, &param.name) {
            continue;
        }

        if let Some(span) = locations::span_of(db, arg.id) {
            hints.push(InlayHintData {
                span,
                kind: InlayHintDataKind::Parameter(param.name.clone()),
            });
        }
    }
}

/// Resolve a call expression to its DefTarget.
fn resolve_call_target(
    db: &Database,
    call: &Call,
    resolutions: &HashMap<NodeId, Resolution>,
    call_sites: &HashMap<NodeId, NodeId>,
) -> Option<DefTarget> {
    // For method calls, use call_resolution
    let callee_name_id = call.call_resolution_id();
    if let Some(&call_expr_id) = call_sites.get(&callee_name_id) {
        if let Some(resolution) = call_resolution(db, call_expr_id) {
            // Prefer impl target (has concrete param names), fall back to trait
            return resolution.impl_target.or(resolution.trait_target);
        }
    }

    // For direct function calls, use name_resolutions on the callee
    let callee_id = match &call.callee.value {
        Expr::Dot(dot) => dot.rhs.id,
        _ => call.callee.id,
    };

    resolutions.get(&callee_id)?.to_def_target()
}

/// Check if an argument expression is a simple variable whose name matches
/// the parameter name.
fn arg_name_matches(arg: &Node<Expr>, param_name: &str) -> bool {
    if let Expr::Name(name) = &arg.value {
        if let Some(n) = name.path.name() {
            return n == param_name;
        }
    }
    false
}
