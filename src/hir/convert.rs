use std::collections::HashMap;

use crate::{
    ast,
    errors::{RayError, RayErrorKind, RayResult},
    pathlib::FilePath,
    span::Span,
    typing::{
        ty::{Ty, TyVar},
        Ctx,
    },
};

use super::{HirNode, HirNodeKind::*, IntoHirNode, Param};

impl IntoHirNode for ast::Expr {
    fn to_hir_node_with(
        &self,
        rest: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        let mut infer_ex = match &self.kind {
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
            ast::ExprKind::Closure(closure) => unimplemented!("to_infer_expr: Closure {}", self),
            ast::ExprKind::Curly(curly) => curly.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::DefaultValue(default_value) => {
                unimplemented!("to_infer_expr: DefaultValue {}", self)
            }
            ast::ExprKind::Dot(dot) => unimplemented!("to_infer_expr: Dot {}", self),
            ast::ExprKind::Fn(f) => f.to_hir_node_with(rest, scope, filepath, ctx)?,
            ast::ExprKind::For(for_ex) => unimplemented!("to_infer_expr: For {}", self),
            ast::ExprKind::If(if_ex) => unimplemented!("to_infer_expr: If {}", self),
            ast::ExprKind::Index(index) => unimplemented!("to_infer_expr: Index {}", self),
            ast::ExprKind::Labeled(label, ex) => unimplemented!("to_infer_expr: Labeled {}", self),
            ast::ExprKind::List(list) => unimplemented!("to_infer_expr: List {}", self),
            ast::ExprKind::Literal(lit) => lit.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Loop(loop_ex) => unimplemented!("to_infer_expr: Loop {}", self),
            ast::ExprKind::Name(name) => name.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::Path(path) => unimplemented!("to_infer_expr: Path {}", self),
            ast::ExprKind::Paren(paren) => unimplemented!("to_infer_expr: Paren {}", self),
            ast::ExprKind::Range(range) => unimplemented!("to_infer_expr: Range {}", self),
            ast::ExprKind::Return(val) => unimplemented!("to_infer_expr: Return {}", self),
            ast::ExprKind::Sequence(sequence) => unimplemented!("to_infer_expr: Sequence {}", self),
            ast::ExprKind::Tuple(tuple) => unimplemented!("to_infer_expr: Tuple {}", self),
            ast::ExprKind::Type(ty) => {
                Const(Ty::ty_type(Ty::from_ast_ty(&ty.kind, &scope, ctx))).into()
            }
            ast::ExprKind::UnaryOp(unary_op) => unary_op.to_hir_node(scope, filepath, ctx)?,
            ast::ExprKind::While(while_ex) => unimplemented!("to_infer_expr: While {}", self),
            ast::ExprKind::Unsafe(ex) => {
                // TODO: mark block as unsafe
                ex.to_hir_node(scope, filepath, ctx)?
            }
        };

        infer_ex.metadata = Some(self.span);
        Ok(infer_ex)
    }
}

impl IntoHirNode for [ast::Expr] {
    #[inline(always)]
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        if let Some((first, rest)) = self.split_first() {
            first.to_hir_node_with(rest, scope, filepath, ctx)
        } else if let Some(first) = self.first() {
            first.to_hir_node(scope, filepath, ctx)
        } else {
            // otherwise it'll be a const of the unit type
            Ok(Const(Ty::unit()).into())
        }
    }
}

impl IntoHirNode for ast::Assign {
    fn to_hir_node_with(
        &self,
        rest: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        let mut vars = vec![];
        let mut rest = rest;
        let mut curr = self;
        loop {
            let lhs = match &curr.lhs.kind {
                ast::ExprKind::Name(n) => n.name.clone(),
                _ => unimplemented!("converting lhs of assign to infer expr: {}", curr.lhs),
            };

            let rhs = if let ast::InfixOp::AssignOp(op) = &curr.op {
                let lhs_operand = Var(lhs.clone()).into();
                let rhs_operand = curr.rhs.to_hir_node(scope, filepath, ctx)?;
                let mut op_var: HirNode<Span> = Var(str!(op.to_string())).into();
                op_var.metadata = Some(curr.op_span);
                Apply(Box::new(op_var), vec![], vec![lhs_operand, rhs_operand]).into()
            } else {
                curr.rhs.to_hir_node(scope, filepath, ctx)?
            };

            vars.push((lhs, rhs));

            if let Some((next, r)) = rest.split_first() {
                if let ast::ExprKind::Assign(a) = &next.kind {
                    curr = a;
                    rest = r;
                    continue;
                }
            }

            break;
        }

        let body = rest.to_hir_node(scope, filepath, ctx)?;
        Ok(Let(vars, Box::new(body)).into())
    }
}

impl IntoHirNode for ast::BinOp {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        let lhs = self.lhs.to_hir_node(scope, filepath, ctx)?;
        let rhs = self.rhs.to_hir_node(scope, filepath, ctx)?;

        let mut op_var: HirNode<Span> = Var(str!(self.op.to_string())).into();
        op_var.metadata = Some(self.op_span);
        Ok(Apply(Box::new(op_var), vec![], vec![lhs, rhs]).into())
    }
}

impl IntoHirNode for ast::Block {
    fn to_hir_node_with(
        &self,
        rest: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        self.stmts.to_hir_node_with(rest, scope, filepath, ctx)
    }
}

impl IntoHirNode for ast::Call {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        if matches!(&self.lhs.kind, ast::ExprKind::Name(n) if &n.name == "sizeof") {
            return Ok(Const(Ty::int()).into());
        }

        let lhs = self.lhs.to_hir_node(scope, filepath, ctx)?;
        let ty_args = self
            .ty_args
            .as_ref()
            .map(|(tys, _)| {
                tys.iter()
                    .map(|t| Ty::from_ast_ty(&t.kind, &scope, ctx))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let args = self
            .args
            .items
            .iter()
            .map(|e| e.to_hir_node(scope, filepath, ctx))
            .collect::<RayResult<Vec<_>>>()?;
        Ok(Apply(Box::new(lhs), ty_args, args).into())
    }
}

impl IntoHirNode for ast::Cast {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        Ok(Const(Ty::from_ast_ty(&self.ty.kind, scope, ctx)).into())
    }
}

impl IntoHirNode for ast::Curly {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        if &self.lhs.name == "struct" {
            unimplemented!("to_hir_node anon struct construction: {}", self)
        }

        let fields = ctx.get_struct_ty(&self.lhs.name).ok_or_else(|| RayError {
            msg: format!("struct type `{}` is undefined", self.lhs),
            fp: FilePath::new(),
            kind: RayErrorKind::Type,
            span: Some(self.lhs.span),
        })?;

        let mut idx = HashMap::new();
        for (i, (f, _)) in fields.iter().enumerate() {
            idx.insert(f.clone(), i);
        }

        let mut param_map = vec![];
        for el in self.elements.iter() {
            let (n, name_span, el) = match &el.kind {
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
                    msg: format!("struct `{}` does not have field `{}`", self.lhs, n),
                    fp: filepath.clone(),
                    kind: RayErrorKind::Type,
                    span: Some(name_span),
                });
            }
        }

        param_map.sort_by_key(|(i, _)| *i);
        let params = param_map.into_iter().map(|(_, el)| el).collect();
        Ok(Apply(
            Box::new(Var(format!("{}::init", self.lhs)).into()),
            vec![],
            params,
        )
        .into())
    }
}

impl IntoHirNode for ast::Fn {
    fn to_hir_node_with(
        &self,
        rest: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        let name = self.sig.name.clone().unwrap();
        let fn_scope = scope.append(name.clone());
        let mut tvs = vec![];
        if let Some(ty_params) = &self.sig.ty_params {
            for tp in ty_params.tys.iter() {
                if let ast::TypeKind::Generic { name, .. } = &tp.kind {
                    let tv = TyVar(name.clone());
                    tvs.push(tv.clone());
                    let ty = Ty::Var(tv);
                    ctx.bind_var(name, ty);
                }
            }
        }

        let params = self
            .sig
            .params
            .iter()
            .map(|n| {
                Param::new(
                    n.name.clone(),
                    n.ty.as_ref()
                        .map(|t| Ty::from_ast_ty(&t.kind, &fn_scope, ctx)),
                )
            })
            .collect::<Vec<_>>();

        let all_typed = params.iter().all(|p| p.get_ty().is_some());
        let none_typed = params.iter().all(|p| p.get_ty().is_none());

        if !all_typed && !none_typed {
            panic!("cannot infer type of only some parameters");
        }

        let fn_body = self
            .body
            .as_ref()
            .unwrap()
            .to_hir_node(&fn_scope, filepath, ctx)?;
        let rhs = if none_typed {
            FunInf(tvs, params, Box::new(fn_body)).into()
        } else {
            Fun(tvs, params, Box::new(fn_body)).into()
        };
        let body = rest.to_hir_node(&scope, filepath, ctx)?;
        Ok(Let(vec![(name, rhs)], Box::new(body)).into())
    }
}

impl IntoHirNode for ast::Literal {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        _: &ast::Path,
        _: &FilePath,
        _: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        Ok(Const(match self {
            ast::Literal::Integer { size, signed, .. } => {
                if *size != 0 {
                    let sign = if !signed { "u" } else { "i" };
                    Ty::Projection(format!("{}{}", sign, size), vec![])
                } else {
                    Ty::IntLiteral
                }
            }
            ast::Literal::Float { size, .. } => {
                if *size != 0 {
                    Ty::Projection(format!("f{}", size), vec![])
                } else {
                    Ty::FloatLiteral
                }
            }
            ast::Literal::String(_) => Ty::string(),
            ast::Literal::ByteString(_) => Ty::string(),
            ast::Literal::Byte(_) => Ty::u8(),
            ast::Literal::Char(_) => Ty::char(),
            ast::Literal::Bool(_) => Ty::bool(),
            ast::Literal::Nil => Ty::nil(),
            ast::Literal::UnicodeEscSeq(_) => unimplemented!("unicode escape sequence"),
        })
        .into())
    }
}

impl IntoHirNode for ast::Name {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        _: &ast::Path,
        _: &FilePath,
        _: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        Ok(Var(self.name.clone()).into())
    }
}

impl IntoHirNode for ast::UnaryOp {
    fn to_hir_node_with(
        &self,
        _: &[ast::Expr],
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode<Span>> {
        let expr = self.expr.to_hir_node(scope, filepath, ctx)?;

        let mut op_var: HirNode<Span> = Var(str!(self.op.to_string())).into();
        op_var.metadata = Some(self.op_span);
        Ok(Apply(Box::new(op_var), vec![], vec![expr]).into())
    }
}
