use std::collections::HashMap;

use ray_shared::{def::DefId, node_id::NodeId, span::Source};

use crate::{
    ast::{
        Assign, BinOp, Closure, Curly, CurlyElement, Expr, FnParam, Func, InfixOp, Node, Pattern,
        Sequence,
    },
    errors::{RayError, RayErrorKind},
    sourcemap::SourceMap,
};

pub fn desugar_compound_assignment(
    assign: &Assign,
    srcmap: &SourceMap,
) -> Result<(Assign, SourceMap), RayError> {
    let mut assign = assign.clone();
    let mut srcmap = srcmap.clone();
    let InfixOp::AssignOp(op) = &mut assign.op else {
        return Ok((assign, srcmap));
    };

    let lhs_src = srcmap.get(&assign.lhs);
    let lhs: Node<Expr> = assign.lhs.clone().try_take_map(|pat| match pat {
        Pattern::Name(_) | Pattern::Dot(_, _) | Pattern::Index(_, _, _) => Ok(pat.into()),
        Pattern::Sequence(_)
        | Pattern::Tuple(_)
        | Pattern::Deref(_)
        | Pattern::Some(_)
        | Pattern::Missing(_) => Err(RayError {
            msg: str!("cannot use expression as l-value for re-assignment"),
            src: vec![lhs_src],
            kind: RayErrorKind::Type,
            context: Some("lower assignment".to_string()),
        }),
    })?;

    // Resume the DefId context so new NodeIds continue from where parsing left off
    // (not reset to 1, which would collide with existing nodes).
    let def_id = assign.lhs.id.owner;
    let _guard = NodeId::resume_def(def_id);

    let new_op = Node::new(InfixOp::Assign);
    let op_src = srcmap.get(op);
    srcmap.set_src(&new_op, op_src);

    let op = std::mem::replace(op.as_mut(), new_op);
    let prev_rhs = assign.rhs.clone();
    let lhs_src = srcmap.get(&lhs);
    let rhs_src = srcmap.get(&prev_rhs);
    let src = lhs_src.extend_to(&rhs_src);
    let rhs = Node::new(Expr::BinOp(BinOp {
        lhs: Box::new(lhs),
        rhs: prev_rhs,
        op,
    }));
    srcmap.set_src(&rhs, src);

    assign.rhs = Box::new(rhs);
    assign.op = InfixOp::Assign;

    Ok((assign, srcmap))
}

pub fn convert_func_to_closure(func: &Func, src: &Source) -> Result<Closure, RayError> {
    if !func.sig.is_anon {
        return Err(RayError {
            msg: "function literals must be anonymous".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    if func.sig.ty_params.is_some() {
        return Err(RayError {
            msg: "function literals cannot declare type parameters yet".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    if !func.sig.qualifiers.is_empty() {
        return Err(RayError {
            msg: "function literals cannot declare where-clauses yet".to_string(),
            src: vec![src.clone()],
            kind: RayErrorKind::Parse,
            context: Some("lower inline function literal".to_string()),
        });
    }
    let body = func.body.clone().ok_or_else(|| RayError {
        msg: "function literal is missing a body".to_string(),
        src: vec![src.clone()],
        kind: RayErrorKind::Parse,
        context: Some("lower inline function literal".to_string()),
    })?;

    let mut params = Vec::with_capacity(func.sig.params.len());
    for param in &func.sig.params {
        match &param.value {
            FnParam::Name { name, .. } => {
                params.push(Node::with_id(param.id, Expr::Name(name.clone())));
            }
            _ => {
                return Err(RayError {
                    msg: "function literal parameters must be simple names".to_string(),
                    src: vec![src.clone()],
                    kind: RayErrorKind::Parse,
                    context: Some("lower inline function literal".to_string()),
                });
            }
        }
    }

    Ok(Closure {
        args: Sequence::new(params),
        body,
        arrow_span: None,
        curly_spans: None,
    })
}

pub fn normalize_curly(
    curly: &Curly,
    src: &Source,
    field_index: &HashMap<String, usize>,
    srcmap: &SourceMap,
    def_id: DefId,
) -> Result<(Curly, SourceMap), RayError> {
    let mut curly = curly.clone();
    let mut srcmap = srcmap.clone();

    let mut param_map = vec![];
    for el in curly.elements.drain(..) {
        let el_span = srcmap.span_of(&el);
        let (name, name_span, el) = match el.value {
            CurlyElement::Name(n) => (n.clone(), el_span, Node::with_id(el.id, Expr::Name(n))),
            CurlyElement::Labeled(n, ex) => (n, el_span, ex),
        };

        let field_name = name.path.name().unwrap();
        if let Some(i) = field_index.get(&field_name) {
            param_map.push((*i, name.clone(), el));
        } else {
            return Err(RayError {
                msg: format!(
                    "struct `{}` does not have field `{}`",
                    curly.lhs.unwrap(),
                    name
                ),
                src: vec![src.respan(name_span)],
                kind: RayErrorKind::Type,
                context: Some("lower curly struct".to_string()),
            });
        }
    }

    param_map.sort_by_key(|(i, ..)| *i);

    let _guard = NodeId::resume_def(def_id);
    let mut elements = vec![];
    for (_, n, el) in param_map.into_iter() {
        let src = srcmap.get(&el);
        let node = Node::new(CurlyElement::Labeled(n, el));
        srcmap.set_src(&node, src);
        srcmap.mark_synthetic(node.id);
        elements.push(node);
    }

    curly.elements = elements;

    Ok((curly, srcmap))
}

/// Expand curly shorthand without field reordering: `Point { x }` -> `Point { x: x }`
///
/// This is used when we can't look up the struct definition to reorder fields,
/// but still need to expand shorthand for downstream passes (e.g., type checking).
pub fn expand_curly_shorthand(curly: &mut Curly, srcmap: &mut SourceMap, def_id: DefId) {
    let _guard = NodeId::resume_def(def_id);

    for elem in &mut curly.elements {
        if let CurlyElement::Name(name) = &elem.value {
            let src = srcmap.get(elem);
            // Inner expression gets the original element's ID (semantic content)
            let name_expr = Node::with_id(elem.id, Expr::Name(name.clone()));
            srcmap.set_src(&name_expr, src.clone());
            // Wrapper element gets a fresh ID
            elem.id = NodeId::new();
            srcmap.mark_synthetic(elem.id);
            elem.value = CurlyElement::Labeled(name.clone(), name_expr);
        }
    }
}
