use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    ast::{self, HasSource, Node, SourceInfo},
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Source,
    typing::{info::TypeInfo, ty::Ty, Ctx},
};

use super::{HirDecl, HirInfo, HirNode, IntoHirNode, Param};
use HirNode::*;

type SourceNode = ast::Node<ast::Expr<SourceInfo>, SourceInfo>;
type OutNode = ast::Node<HirNode<SourceInfo>, SourceInfo>;

impl IntoHirNode<SourceInfo> for SourceNode {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        _: u64,
        _: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let id = self.id;
        let info = self.info;
        Ok(match self.value {
            ast::Expr::Break(val) => {
                if let Some(val) = val {
                    unimplemented!()
                } else {
                    unimplemented!()
                }
            }

            ast::Expr::Assign(assign) => assign.to_hir_node_with(rest, scope, id, &info, ctx)?,
            ast::Expr::Block(block) => block.to_hir_node_with(rest, scope, id, &info, ctx)?,
            ast::Expr::BinOp(binop) => binop.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::Call(call) => call.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::Cast(cast) => cast.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::Closure(closure) => unimplemented!("to_infer_expr: Closure"),
            ast::Expr::Curly(curly) => curly.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::DefaultValue(default_value) => {
                unimplemented!("to_infer_expr: DefaultValue")
            }
            ast::Expr::Dot(dot) => unimplemented!("to_infer_expr: Dot"),
            ast::Expr::Fn(f) => f.to_hir_node_with(rest, scope, id, &info, ctx)?,
            ast::Expr::For(for_ex) => unimplemented!("to_infer_expr: For"),
            ast::Expr::If(if_ex) => unimplemented!("to_infer_expr: If"),
            ast::Expr::Index(index) => unimplemented!("to_infer_expr: Index"),
            ast::Expr::Labeled(label, ex) => unimplemented!("to_infer_expr: Labeled"),
            ast::Expr::List(list) => unimplemented!("to_infer_expr: List"),
            ast::Expr::Literal(lit) => lit.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::Loop(loop_ex) => unimplemented!("to_infer_expr: Loop"),
            ast::Expr::Name(name) => name.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::Path(path) => unimplemented!("to_infer_expr: Path"),
            ast::Expr::Paren(paren) => unimplemented!("to_infer_expr: Paren"),
            ast::Expr::Range(range) => unimplemented!("to_infer_expr: Range"),
            ast::Expr::Return(val) => unimplemented!("to_infer_expr: Return"),
            ast::Expr::Sequence(sequence) => unimplemented!("to_infer_expr: Sequence"),
            ast::Expr::Tuple(tuple) => unimplemented!("to_infer_expr: Tuple"),
            ast::Expr::Type(ty) => ast::Node {
                id,
                info,
                value: Type(Ty::ty_type(Ty::from_ast_ty(&ty.kind, &scope, ctx))),
            },
            ast::Expr::UnaryOp(unary_op) => unary_op.to_hir_node(scope, id, &info, ctx)?,
            ast::Expr::While(while_ex) => unimplemented!("to_infer_expr: While"),
            ast::Expr::Unsafe(ex) => {
                // TODO: mark block as unsafe
                ex.to_hir_node(scope, id, &info, ctx)?
            }
        })
    }
}

// impl IntoHirNode<SourceInfo> for VecDeque<SourceNode><SourceInfo> {
//     #[inline(always)]
//     fn to_hir_node_with(
//         &self,
//         rest: &mut VecDeque<SourceNode>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut Ctx,
//     ) -> RayResult<Self::Output> {
//         if let Some(first) = rest.pop_front() {
//             first.to_hir_node_with(rest, scope, id, info, ctx)
//         } else {
//             // otherwise it'll be a const unit
//             Ok(Literal(ast::Literal::Unit))
//         }
//     }
// }

impl IntoHirNode<SourceInfo> for ast::Assign<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let mut vars = vec![];
        let mut id = id;
        let mut curr_info = info.clone();
        let mut curr = self;
        let mut lhs_vars = HashSet::new();
        loop {
            let (lhs_id, lhs_value, lhs_info) = curr.lhs.unpack();
            // let (rhs_id, rhs_value, rhs_info) = curr.rhs.unpack();
            let lhs = match &lhs_value {
                ast::Expr::Name(n) => n.name.clone(),
                _ => unimplemented!("converting lhs of assign to infer expr: {}", lhs_value),
            };

            lhs_vars.insert(lhs.clone());

            let rhs_src = curr.rhs.src();
            let lhs_src = lhs_info.src();
            let rhs = if let ast::InfixOp::AssignOp(op) = &curr.op {
                let lhs_operand = Node {
                    id: lhs_id,
                    value: Var(lhs.clone()),
                    info: lhs_info,
                };

                let rhs_id = curr.rhs.id;
                let rhs_info = curr.rhs.info.clone();
                let rhs_operand = curr.rhs.to_hir_node(scope, rhs_id, &rhs_info, ctx)?;
                let op_var = Node {
                    id: rhs_id,
                    value: Var(str!(op.to_string())),
                    info: SourceInfo::new(Source {
                        filepath: curr_info.src.filepath.clone(),
                        span: Some(curr.op_span),
                    }),
                };
                Node {
                    id: rhs_id,
                    info: rhs_info,
                    value: Apply(Box::new(op_var), vec![lhs_operand, rhs_operand]),
                }
            } else {
                curr.rhs.to_hir_node(scope, id, &curr_info, ctx)?
            };

            let mut info = curr_info.clone();
            info.src = lhs_src.extend_to(&rhs_src);
            vars.push(Node {
                id,
                info,
                value: HirDecl::var(lhs, rhs),
            });

            if let Some(next) = rest.pop_front() {
                if let ast::Expr::Assign(a) = next.value {
                    let rhs_vars = a.rhs.get_vars();
                    if !lhs_vars
                        .iter()
                        .collect::<HashSet<_>>()
                        .is_disjoint(&rhs_vars)
                    {
                        // if there are variables on the RHS that were
                        // previously defined we have to stop here
                        break;
                    }

                    id = next.id;
                    curr_info = next.info;
                    curr = a;
                    continue;
                }

                // otherwise, put it back
                rest.push_front(next);
            }

            break;
        }

        let body = HirNode::block(rest, scope, id, &curr_info, ctx)?;
        Ok(Node {
            id,
            info: curr_info,
            value: Let(vars, Box::new(body)),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::BinOp<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let lhs = self.lhs.to_hir_node(scope, id, info, ctx)?;
        let rhs = self.rhs.to_hir_node(scope, id, info, ctx)?;

        let mut name = self.op.to_string();
        if let Some(fqn) = ctx.lookup_fqn(&name) {
            name = fqn.to_string();
        }

        let op_var = Node::new(
            Var(name),
            SourceInfo::new(Source {
                span: Some(self.op_span),
                filepath: info.src.filepath.clone(),
            }),
        );
        Ok(Node {
            id,
            info: info.clone(),
            value: Apply(Box::new(op_var), vec![lhs, rhs]),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::Block<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let mut stmts = self.stmts.into_iter().collect::<VecDeque<_>>();
        HirNode::block(&mut stmts, scope, id, info, ctx)
    }
}

impl IntoHirNode<SourceInfo> for ast::Call<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let lhs = self.lhs.to_hir_node(scope, id, info, ctx)?;
        let args = self.args.items.to_hir_node(scope, id, info, ctx)?;
        Ok(Node {
            id,
            info: info.clone(),
            value: Apply(Box::new(lhs), args),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::Cast<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let ty = Ty::from_ast_ty(&self.ty.kind, scope, ctx);
        Ok(Node {
            id,
            info: info.clone(),
            value: Cast(Box::new(self.to_hir_node(scope, id, info, ctx)?), ty),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::Curly<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        if self.lhs.is_none() {
            unimplemented!("to_hir_node anon struct construction: {}", self)
        }

        let lhs = self.lhs.as_ref().unwrap();
        let struct_fqn = match ctx.lookup_fqn(&lhs.name) {
            Some(fqn) => fqn.clone(),
            _ => {
                return Err(RayError {
                    msg: format!("struct type `{}` is undefined", lhs),
                    src: vec![Source {
                        span: Some(lhs.span),
                        filepath: FilePath::new(),
                    }],
                    kind: RayErrorKind::Type,
                })
            }
        };

        let struct_ty = match ctx.get_struct_ty(&struct_fqn) {
            Some(t) => t,
            _ => {
                return Err(RayError {
                    msg: format!("struct type `{}` is undefined", lhs),
                    src: vec![Source {
                        span: Some(lhs.span),
                        filepath: FilePath::new(),
                    }],
                    kind: RayErrorKind::Type,
                })
            }
        };

        let mut idx = HashMap::new();
        for (i, (f, _)) in struct_ty.fields.iter().enumerate() {
            idx.insert(f.clone(), i);
        }

        let mut param_map = vec![];
        for el in self.elements.into_iter() {
            let (n, name_span, el) = match el.kind {
                ast::CurlyElementKind::Name(n) => {
                    (n.to_string(), n.span, n.to_hir_node(scope, id, info, ctx)?)
                }
                ast::CurlyElementKind::Labeled(n, ex) => {
                    (n.to_string(), n.span, ex.to_hir_node(scope, id, info, ctx)?)
                }
            };

            if let Some(i) = idx.get(&n) {
                param_map.push((*i, el));
            } else {
                return Err(RayError {
                    msg: format!("struct `{}` does not have field `{}`", lhs, n),
                    src: vec![Source {
                        span: Some(name_span),
                        filepath: info.src.filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                });
            }
        }

        param_map.sort_by_key(|(i, _)| *i);
        let params = param_map.into_iter().map(|(_, el)| el).collect();
        let v = Node::new(Var(format!("{}::init", struct_fqn)), info.clone());
        Ok(Node {
            id,
            info: info.clone(),
            value: Apply(Box::new(v), params),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::Fn<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let name = self.sig.name.clone().unwrap();
        let fn_scope = scope.append(name.clone());
        let mut fn_ctx = ctx.clone();
        let mut params = vec![];
        for p in self.sig.params.iter() {
            let n = match p.name() {
                Some(n) => n.clone(),
                _ => {
                    return Err(RayError {
                        msg: str!("parameter has no name"),
                        src: vec![Source {
                            span: Some(p.span()),
                            filepath: info.src.filepath.clone(),
                        }],
                        kind: RayErrorKind::Type,
                    })
                }
            };

            params.push(Param::new(
                n,
                p.ty()
                    .map(|t| Ty::from_ast_ty(&t.kind, &fn_scope, &mut fn_ctx)),
            ));
        }

        let param_tys = params
            .iter()
            .map(|p| p.get_ty().cloned())
            .collect::<Vec<_>>();

        let num_typed = param_tys
            .iter()
            .fold(0, |acc, p| if p.is_some() { acc + 1 } else { acc });

        if num_typed != 0 && num_typed != param_tys.len() {
            panic!("cannot infer type of only some parameters");
        }

        let body = self.body.unwrap();
        let body_id = body.id;
        let body_info = body.info.clone();
        let fn_body = body.to_hir_node(&fn_scope, body_id, &body_info, ctx)?;

        let mut rhs = Node {
            id: body_id,
            info: body_info.clone(),
            value: Fun(params, Box::new(fn_body)),
        };
        if num_typed == param_tys.len() {
            let ty = Ty::from_sig(&self.sig, &fn_scope, &info.src.filepath, &mut fn_ctx, ctx)?;
            rhs = Node {
                id: rhs.id,
                info: rhs.info.clone(),
                value: HirNode::Typed(Box::new(Node {
                    id: rhs.id,
                    info: HirInfo {
                        src_info: rhs.info,
                        ty_info: TypeInfo::new(ty),
                    },
                    value: rhs.value,
                })),
            };
        }

        let body = HirNode::block(rest, &scope, body_id, &body_info, ctx)?;
        let span = self.span.extend_to(&body.src().span.unwrap());
        Ok(Node::new(
            Let(
                vec![Node {
                    id,
                    info: info.clone(),
                    value: HirDecl::var(name, rhs),
                }],
                Box::new(body),
            ),
            SourceInfo::new(Source {
                filepath: info.src.filepath.clone(),
                span: Some(span),
            }),
        ))
    }
}

impl IntoHirNode<SourceInfo> for ast::Literal {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        _: &ast::Path,
        id: u64,
        info: &SourceInfo,
        _: &mut Ctx,
    ) -> RayResult<Self::Output> {
        Ok(Node {
            id,
            info: info.clone(),
            value: Literal(self.clone()),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::Name {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        _: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        log::debug!("lookup fqn: {}", self.name);
        let name = if let Some(fqn) = ctx.lookup_fqn(&self.name) {
            log::debug!("fqn for `{}`: {}", self.name, fqn);
            fqn.to_string()
        } else {
            self.name.clone()
        };

        Ok(Node {
            id,
            info: info.clone(),
            value: Var(name),
        })
    }
}

impl IntoHirNode<SourceInfo> for ast::UnaryOp<SourceInfo> {
    type Output = OutNode;

    fn to_hir_node_with(
        self,
        _: &mut VecDeque<SourceNode>,
        scope: &ast::Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Self::Output> {
        let expr = self.expr.to_hir_node(scope, id, info, ctx)?;
        let op_var = Node::new(
            Var(str!(self.op.to_string())),
            SourceInfo::new(Source {
                span: Some(self.op_span),
                filepath: info.src.filepath.clone(),
            }),
        );
        Ok(Node {
            id,
            info: info.clone(),
            value: Apply(Box::new(op_var), vec![expr]),
        })
    }
}
