use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    ast,
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Source,
    typing::{ty::Ty, Ctx},
};

use super::{HirDecl, HirNode, HirNodeKind::*, IntoHirNode, Param, TypedHirNode};

impl IntoHirNode for ast::Expr {
    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let mut infer_ex = match self.kind {
            ast::ExprKind::Break(val) => {
                if let Some(val) = val {
                    unimplemented!()
                } else {
                    unimplemented!()
                }
            }

            ast::ExprKind::Assign(assign) => assign.to_hir_node_with(rest, scope, filepath, ctx)?,
            ast::ExprKind::Block(block) => block.to_hir_node_with(rest, scope, filepath, ctx)?,
            ast::ExprKind::BinOp(binop) => binop.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Call(call) => call.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Cast(cast) => cast.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Closure(closure) => unimplemented!("to_infer_expr: Closure"),
            ast::ExprKind::Curly(curly) => curly.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::DefaultValue(default_value) => {
                unimplemented!("to_infer_expr: DefaultValue")
            }
            ast::ExprKind::Dot(dot) => unimplemented!("to_infer_expr: Dot"),
            ast::ExprKind::Fn(f) => f.to_hir_node_with(rest, scope, filepath, ctx)?,
            ast::ExprKind::For(for_ex) => unimplemented!("to_infer_expr: For"),
            ast::ExprKind::If(if_ex) => unimplemented!("to_infer_expr: If"),
            ast::ExprKind::Index(index) => unimplemented!("to_infer_expr: Index"),
            ast::ExprKind::Labeled(label, ex) => unimplemented!("to_infer_expr: Labeled"),
            ast::ExprKind::List(list) => unimplemented!("to_infer_expr: List"),
            ast::ExprKind::Literal(lit) => lit.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Loop(loop_ex) => unimplemented!("to_infer_expr: Loop"),
            ast::ExprKind::Name(name) => name.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Path(path) => unimplemented!("to_infer_expr: Path"),
            ast::ExprKind::Paren(paren) => unimplemented!("to_infer_expr: Paren"),
            ast::ExprKind::Range(range) => unimplemented!("to_infer_expr: Range"),
            ast::ExprKind::Return(val) => unimplemented!("to_infer_expr: Return"),
            ast::ExprKind::Sequence(sequence) => unimplemented!("to_infer_expr: Sequence"),
            ast::ExprKind::Tuple(tuple) => unimplemented!("to_infer_expr: Tuple"),
            ast::ExprKind::Type(ty) => {
                Type(Ty::ty_type(Ty::from_ast_ty(&ty.kind, &scope, ctx))).into()
            }
            ast::ExprKind::UnaryOp(unary_op) => unary_op.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::While(while_ex) => unimplemented!("to_infer_expr: While"),
            ast::ExprKind::Unsafe(ex) => {
                // TODO: mark block as unsafe
                ex.to_hir_node(scope, filepath, ctx)?
            }
        };

        infer_ex.src = Some(self.src.clone());
        Ok(infer_ex)
    }
}

// impl IntoHirNode for VecDeque<ast::Expr> {
//     #[inline(always)]
//     fn to_hir_node_with(
//         &self,
//         rest: &mut VecDeque<ast::Expr>,
//         scope: &ast::Path,
//         filepath: &FilePath,
//         ctx: &mut Ctx,
//     ) -> RayResult<HirNode> {
//         if let Some(first) = rest.pop_front() {
//             first.to_hir_node_with(rest, scope, filepath, ctx)
//         } else {
//             // otherwise it'll be a const unit
//             Ok(Literal(ast::Literal::Unit).into())
//         }
//     }
// }

impl IntoHirNode for ast::Assign {
    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let mut vars = vec![];
        let mut curr = self;
        let mut lhs_vars = HashSet::new();
        loop {
            let lhs = match &curr.lhs.kind {
                ast::ExprKind::Name(n) => n.name.clone(),
                _ => unimplemented!("converting lhs of assign to infer expr: {}", curr.lhs),
            };

            lhs_vars.insert(lhs.clone());

            let rhs_src = curr.rhs.src.clone();
            let rhs = if let ast::InfixOp::AssignOp(op) = &curr.op {
                let lhs_operand = Var(lhs.clone()).into();
                let rhs_operand = curr.rhs.to_hir_node(scope, filepath, ctx)?;
                let mut op_var: HirNode = Var(str!(op.to_string())).into();
                op_var.src = Some(Source {
                    filepath: filepath.clone(),
                    span: Some(curr.op_span),
                });
                Apply(Box::new(op_var), vec![lhs_operand, rhs_operand]).into()
            } else {
                curr.rhs.to_hir_node(scope, filepath, ctx)?
            };

            let span = curr.lhs.src.extend_to(&rhs_src);
            vars.push(HirDecl::var(lhs, rhs).with_src(Some(span)));

            if let Some(next) = rest.pop_front() {
                if let ast::ExprKind::Assign(a) = next.kind {
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

                    curr = a;
                    continue;
                }

                // otherwise, put it back
                rest.push_front(next);
            }

            break;
        }

        let body = HirNode::block(rest, scope, filepath, ctx)?;
        Ok(Let(vars, Box::new(body)).into())
    }
}

impl IntoHirNode for ast::BinOp {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let lhs = self.lhs.to_hir_node(scope, filepath, ctx)?;
        let rhs = self.rhs.to_hir_node(scope, filepath, ctx)?;

        let mut name = self.op.to_string();
        if let Some(fqn) = ctx.lookup_fqn(&name) {
            name = fqn.to_string();
        }

        let mut op_var: HirNode = Var(name).into();
        op_var.src = Some(Source {
            span: Some(self.op_span),
            filepath: filepath.clone(),
        });
        Ok(Apply(Box::new(op_var), vec![lhs, rhs]).into())
    }
}

impl IntoHirNode for ast::Block {
    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let mut stmts = self.stmts.into_iter().collect::<VecDeque<_>>();
        HirNode::block(&mut stmts, scope, filepath, ctx)
    }
}

impl IntoHirNode for ast::Call {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let lhs = self.lhs.to_hir_node(scope, filepath, ctx)?;
        let args = self
            .args
            .items
            .into_iter()
            .map(|e| e.to_hir_node(scope, filepath, ctx))
            .collect::<RayResult<Vec<_>>>()?;
        Ok(Apply(Box::new(lhs), args).into())
    }
}

impl IntoHirNode for ast::Cast {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let ty = Ty::from_ast_ty(&self.ty.kind, scope, ctx);
        Ok(Cast(Box::new(self.to_hir_node(scope, filepath, ctx)?), ty).into())
    }
}

impl IntoHirNode for ast::Curly {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
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
                    (n.to_string(), n.span, n.to_hir_node(scope, filepath, ctx)?)
                }
                ast::CurlyElementKind::Labeled(n, ex) => {
                    (n.to_string(), n.span, ex.to_hir_node(scope, filepath, ctx)?)
                }
            };

            if let Some(i) = idx.get(&n) {
                param_map.push((*i, el));
            } else {
                return Err(RayError {
                    msg: format!("struct `{}` does not have field `{}`", lhs, n),
                    src: vec![Source {
                        span: Some(name_span),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                });
            }
        }

        param_map.sort_by_key(|(i, _)| *i);
        let params = param_map.into_iter().map(|(_, el)| el).collect();
        Ok(Apply(
            Box::new(Var(format!("{}::init", struct_fqn)).into()),
            params,
        )
        .into())
    }
}

impl IntoHirNode for ast::Fn {
    fn to_hir_node_with(
        self,
        rest: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
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
                            filepath: filepath.clone(),
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

        let fn_body = self.body.unwrap().to_hir_node(&fn_scope, filepath, ctx)?;

        let mut rhs = Fun(params, Box::new(fn_body)).into();
        if num_typed == param_tys.len() {
            let fn_ty = Ty::from_sig(&self.sig, &fn_scope, filepath, &mut fn_ctx, ctx)?;
            rhs = TypedHirNode::new(rhs, fn_ty).into();
        }

        let body = HirNode::block(rest, &scope, filepath, ctx)?;
        Ok(Let(
            vec![HirDecl::var(name, rhs).with_src(Some(Source {
                span: Some(self.span),
                filepath: filepath.clone(),
            }))],
            Box::new(body),
        )
        .into())
    }
}

impl IntoHirNode for ast::Literal {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        _: &ast::Path,
        _: &FilePath,
        _: &mut Ctx,
    ) -> RayResult<HirNode> {
        Ok(Literal(self.clone()).into())
    }
}

impl IntoHirNode for ast::Name {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        _: &ast::Path,
        _: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        log::debug!("lookup fqn: {}", self.name);
        let name = if let Some(fqn) = ctx.lookup_fqn(&self.name) {
            log::debug!("fqn for `{}`: {}", self.name, fqn);
            fqn.to_string()
        } else {
            self.name.clone()
        };

        Ok(Var(name).into())
    }
}

impl IntoHirNode for ast::UnaryOp {
    fn to_hir_node_with(
        self,
        _: &mut VecDeque<ast::Expr>,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let expr = self.expr.to_hir_node(scope, filepath, ctx)?;

        let mut op_var: HirNode = Var(str!(self.op.to_string())).into();
        op_var.src = Some(Source {
            span: Some(self.op_span),
            filepath: filepath.clone(),
        });
        Ok(Apply(Box::new(op_var), vec![expr]).into())
    }
}
