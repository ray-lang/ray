// use std::{
//     collections::{HashMap, HashSet, VecDeque},
//     ops::Deref,
// };

// use crate::{
//     ast::{self, HasSource, Node, Path, SourceInfo},
//     errors::{RayError, RayErrorKind, RayResult},
//     pathlib::FilePath,
//     span::{Source, Span},
//     typing::{info::TypeInfo, ty::Ty, TyCtx},
// };

// use super::{HirDecl, HirField, HirInfo, HirNode, IntoHirNode, Param};
// use ast::{InfixOp, PrefixOp};
// use HirNode::*;

// type Node = ast::Node<ast::Expr>;
// type OutNode = ast::Node<HirNode>;

// impl IntoHirNode for Node {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         _: u64,
//         _: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let id = self.id;
//         let info = self.info;
//         Ok(match self.value {
//             ast::Expr::Break(val) => {
//                 if let Some(val) = val {
//                     unimplemented!()
//                 } else {
//                     unimplemented!()
//                 }
//             }

//             ast::Expr::Assign(assign) => assign.to_hir_node_with(rest, scope, id, &info, ctx)?,
//             ast::Expr::Asm(asm) => asm.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Block(block) => block.to_hir_node_with(rest, scope, id, &info, ctx)?,
//             ast::Expr::BinOp(binop) => binop.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Call(call) => call.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Cast(cast) => cast.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Closure(closure) => unimplemented!("to_infer_expr: Closure"),
//             ast::Expr::Curly(curly) => curly.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::DefaultValue(default_value) => {
//                 unimplemented!("to_infer_expr: DefaultValue")
//             }
//             ast::Expr::Dot(dot) => dot.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Fn(f) => f.to_hir_node_with(rest, &info.path, id, &info, ctx)?,
//             ast::Expr::For(for_ex) => unimplemented!("to_infer_expr: For"),
//             ast::Expr::If(if_ex) => unimplemented!("to_infer_expr: If"),
//             ast::Expr::Index(index) => unimplemented!("to_infer_expr: Index"),
//             ast::Expr::Labeled(label, ex) => unimplemented!("to_infer_expr: Labeled"),
//             ast::Expr::List(list) => list.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Literal(lit) => lit.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Loop(loop_ex) => unimplemented!("to_infer_expr: Loop"),
//             ast::Expr::Name(name) => name.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Path(path) => unimplemented!("to_infer_expr: Path"),
//             ast::Expr::Paren(paren) => paren.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Range(range) => range.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Return(val) => unimplemented!("to_infer_expr: Return"),
//             ast::Expr::Sequence(sequence) => unimplemented!("to_infer_expr: Sequence"),
//             ast::Expr::Tuple(tuple) => tuple.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::Type(ty) => Node {
//                 id,
//                 info,
//                 value: Type(Ty::ty_type(ty.take_value().resolve_ty(&scope, ctx))),
//             },
//             ast::Expr::TypeAnnotated(value, ty) => {
//                 let value_id = value.id;
//                 let value_info = value.info.clone();
//                 let new_value = value.to_hir_node(scope, id, &info, ctx)?;
//                 Node {
//                     id,
//                     info,
//                     value: HirNode::Typed(Box::new(Node {
//                         id: value_id,
//                         info: HirInfo {
//                             src_info: value_info,
//                             ty_info: TypeInfo::new(ty.value.clone_value().resolve_ty(&scope, ctx)),
//                         },
//                         value: new_value.value,
//                     })),
//                 }
//             }
//             ast::Expr::UnaryOp(unary_op) => unary_op.to_hir_node(scope, id, &info, ctx)?,
//             ast::Expr::While(while_ex) => unimplemented!("to_infer_expr: While"),
//             ast::Expr::Unsafe(ex) => {
//                 // TODO: mark block as unsafe
//                 ex.to_hir_node(scope, id, &info, ctx)?
//             }
//         })
//     }
// }

// impl IntoHirNode for ast::asm::Asm {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node<ast::Expr>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let ret_ty = self
//             .ret_ty
//             .as_ref()
//             .map(|t| t.clone_value().resolve_ty(scope, ctx));
//         Ok(Node {
//             id,
//             value: HirNode::Asm(ret_ty, self.inst),
//             info: info.clone(),
//         })
//     }
// }

// impl IntoHirNode for ast::Assign {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         fn convert_assign_op(
//             op: &ast::InfixOp,
//             op_span: Span,
//             lhs: (u64, HirNode, SourceInfo),
//             rhs: Node,
//             scope: &ast::Path,
//             ctx: &mut TyCtx,
//         ) -> RayResult<OutNode> {
//             let (lhs_id, lhs_value, lhs_info) = lhs;
//             let lhs_operand = Node {
//                 id: lhs_id,
//                 value: lhs_value,
//                 info: lhs_info,
//             };

//             let rhs_id = rhs.id;
//             let rhs_info = rhs.info.clone();
//             let rhs_operand = rhs.to_hir_node(scope, rhs_id, &rhs_info, ctx)?;
//             let name = op.to_string();
//             let fqn = if let Some(fqn) = ctx.lookup_fqn(&name) {
//                 fqn.clone()
//             } else {
//                 Path::from(name)
//             };
//             let op_var = Node {
//                 id: rhs_id,
//                 value: Var(fqn),
//                 info: SourceInfo::new(Source {
//                     filepath: rhs_info.src.filepath.clone(),
//                     span: Some(op_span),
//                 }),
//             };
//             Ok(Node {
//                 id: rhs_id,
//                 info: rhs_info,
//                 value: Apply(Box::new(op_var), vec![lhs_operand, rhs_operand]),
//             })
//         }

//         let mut vars = vec![];
//         let info = info.clone();
//         let (lhs_id, lhs_value, lhs_info) = self.lhs.unpack();
//         let lhs = match lhs_value {
//             ast::Expr::Name(n) => Path::from(n.name.clone()),
//             ast::Expr::UnaryOp(unop) if unop.op == ast::PrefixOp::Deref => {
//                 let lhs = unop.expr.to_hir_node(scope, lhs_id, &info, ctx)?;
//                 let rhs = if let ast::InfixOp::AssignOp(_) = &self.op {
//                     unimplemented!()
//                 } else {
//                     self.rhs.to_hir_node(scope, id, &info, ctx)?
//                 };
//                 return Ok(Node {
//                     id,
//                     info,
//                     value: DerefAssign(Box::new(lhs), Box::new(rhs)),
//                 });
//             }
//             l => unimplemented!("converting lhs of assign to infer expr: {}", l),
//         };

//         let rhs_src = self.rhs.src();
//         let lhs_src = lhs_info.src();
//         let rhs = if let ast::InfixOp::AssignOp(op) = &self.op {
//             convert_assign_op(
//                 op,
//                 self.op_span,
//                 (lhs_id, Var(lhs.clone()), lhs_info),
//                 *self.rhs,
//                 scope,
//                 ctx,
//             )?
//         } else {
//             self.rhs.to_hir_node(scope, id, &info, ctx)?
//         };

//         let mut info = info.clone();
//         info.src = lhs_src.extend_to(&rhs_src);
//         vars.push(Node {
//             id,
//             info: info.clone(),
//             value: HirDecl::var(lhs, rhs),
//         });

//         let body = HirNode::block(rest, scope, id, &info, ctx)?;
//         Ok(Node {
//             id,
//             info,
//             value: Let(vars, Box::new(body)),
//         })
//     }
// }

// impl IntoHirNode for ast::BinOp {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let lhs = self.lhs.to_hir_node(scope, id, info, ctx)?;
//         let rhs = self.rhs.to_hir_node(scope, id, info, ctx)?;

//         let name = self.op.to_string();
//         let fqn = if let Some(fqn) = ctx.lookup_fqn(&name) {
//             fqn.clone()
//         } else {
//             Path::from(name)
//         };

//         let op_var = Node::new(
//             Var(fqn),
//             SourceInfo::new(Source {
//                 span: Some(self.op_span),
//                 filepath: info.src.filepath.clone(),
//             }),
//         );
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Apply(Box::new(op_var), vec![lhs, rhs]),
//         })
//     }
// }

// impl IntoHirNode for ast::Block {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let mut stmts = self.stmts.into_iter().collect::<VecDeque<_>>();
//         HirNode::block(&mut stmts, scope, id, info, ctx)
//     }
// }

// impl IntoHirNode for ast::Call {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         // let fqn = match &self.lhs.value {
//         //     ast::Expr::Dot(d) => ctx.lookup_fqn(&d.rhs.name).cloned(),
//         //     _ => None,
//         // };

//         // let mut args = vec![];
//         // let lhs = if let Some(fqn) = fqn {
//         //     let d = variant!(self.lhs.value, if ast::Expr::Dot(d));
//         //     args.push(d.lhs.to_hir_node(scope, id, info, ctx)?);
//         //     Node::new(
//         //         Var(fqn.to_string()),
//         //         SourceInfo::new(Source {
//         //             filepath: info.src.filepath.clone(),
//         //             span: Some(d.rhs.span),
//         //         }),
//         //     )
//         // } else {
//         //     self.lhs.to_hir_node(scope, id, info, ctx)?
//         // };

//         // args.extend(self.args.items.to_hir_node(scope, id, info, ctx)?);
//         let lhs = self.lhs.to_hir_node(scope, id, info, ctx)?;
//         let args = self.args.items.to_hir_node(scope, id, info, ctx)?;
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Apply(Box::new(lhs), args),
//         })
//     }
// }

// impl IntoHirNode for ast::Cast {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let ty = self.ty.clone_value().resolve_ty(scope, ctx);
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Cast(Box::new(self.lhs.to_hir_node(scope, id, info, ctx)?), ty),
//         })
//     }
// }

// impl IntoHirNode for ast::Curly {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         if self.lhs.is_none() {
//             unimplemented!("to_hir_node anon struct construction: {}", self)
//         }

//         let lhs = self.lhs.as_ref().unwrap();
//         let struct_fqn = match ctx.lookup_fqn(&lhs.name) {
//             Some(fqn) => fqn.clone(),
//             _ => {
//                 return Err(RayError {
//                     msg: format!("struct type `{}` is undefined", lhs),
//                     src: vec![Source {
//                         span: Some(lhs.span),
//                         filepath: FilePath::new(),
//                     }],
//                     kind: RayErrorKind::Type,
//                 })
//             }
//         };

//         let struct_ty = match ctx.get_struct_ty(&struct_fqn) {
//             Some(t) => t,
//             _ => {
//                 return Err(RayError {
//                     msg: format!("struct type `{}` is undefined", lhs),
//                     src: vec![Source {
//                         span: Some(lhs.span),
//                         filepath: FilePath::new(),
//                     }],
//                     kind: RayErrorKind::Type,
//                 })
//             }
//         };

//         let mut ty = struct_ty.ty.clone();
//         let mut idx = HashMap::new();
//         for (i, (f, _)) in struct_ty.fields.iter().enumerate() {
//             idx.insert(f.clone(), i);
//         }

//         let mut param_map = vec![];
//         for el in self.elements.into_iter() {
//             let (n, name_span, el) = match el.value {
//                 ast::CurlyElement::Name(n) => (
//                     n.to_string(),
//                     el.span(),
//                     n.to_hir_node(scope, id, info, ctx)?,
//                 ),
//                 ast::CurlyElement::Labeled(n, ex) => (
//                     n.to_string(),
//                     el.span(),
//                     ex.to_hir_node(scope, id, info, ctx)?,
//                 ),
//             };

//             if let Some(i) = idx.get(&n) {
//                 param_map.push((*i, n.clone(), el));
//             } else {
//                 return Err(RayError {
//                     msg: format!("struct `{}` does not have field `{}`", lhs, n),
//                     src: vec![Source {
//                         span: Some(name_span),
//                         filepath: info.src.filepath.clone(),
//                     }],
//                     kind: RayErrorKind::Type,
//                 });
//             }
//         }

//         param_map.sort_by_key(|(i, ..)| *i);
//         let params = param_map.into_iter().map(|(_, n, el)| (n, el)).collect();
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Struct(struct_fqn, ty, params),
//         })
//     }
// }

// impl IntoHirNode for ast::Dot {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let lhs = self.lhs.to_hir_node(scope, id, info, ctx)?;
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Dot(
//                 Box::new(lhs),
//                 Node::new(HirField::new(self.rhs.name), info.clone()),
//             ),
//         })
//     }
// }

// impl IntoHirNode for ast::Fn {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let name = self.sig.name.clone().unwrap();
//         let mut fn_fqn = ast::Path::from(name.clone());
//         if fn_fqn.len() == 1 {
//             fn_fqn = scope.clone();
//         }

//         ctx.add_fqn(name.clone(), fn_fqn.clone());

//         let mut fn_ctx = ctx.clone();
//         let mut params = vec![];
//         for p in self.sig.params.iter() {
//             let n = match p.name() {
//                 Some(n) => n.clone(),
//                 _ => {
//                     return Err(RayError {
//                         msg: str!("parameter has no name"),
//                         src: vec![Source {
//                             span: Some(p.span()),
//                             filepath: info.src.filepath.clone(),
//                         }],
//                         kind: RayErrorKind::Type,
//                     })
//                 }
//             };

//             params.push(Param::new(
//                 n,
//                 p.ty().map(|t| t.clone().resolve_ty(&fn_fqn, &mut fn_ctx)),
//             ));
//         }

//         let param_tys = params
//             .iter()
//             .map(|p| p.get_ty().cloned())
//             .collect::<Vec<_>>();

//         let num_typed = param_tys
//             .iter()
//             .fold(0, |acc, p| if p.is_some() { acc + 1 } else { acc });

//         if num_typed != 0 && num_typed != param_tys.len() {
//             panic!("cannot infer type of only some parameters");
//         }

//         let body = self.body.unwrap();
//         let body_id = body.id;
//         let body_info = body.info.clone();
//         let fn_body = body.to_hir_node(&fn_fqn, body_id, &body_info, ctx)?;

//         let mut rhs = Node {
//             id: body_id,
//             info: body_info.clone(),
//             value: Fn(params, Box::new(fn_body), self.sig.decorators.clone()),
//         };
//         if num_typed == param_tys.len() {
//             let ty = Ty::from_sig(&self.sig, &fn_fqn, &info.src.filepath, &mut fn_ctx, ctx)?;
//             rhs = Node {
//                 id: rhs.id,
//                 info: rhs.info.clone(),
//                 value: HirNode::Typed(Box::new(Node {
//                     id: rhs.id,
//                     info: HirInfo {
//                         src_info: rhs.info,
//                         ty_info: TypeInfo::new(ty),
//                     },
//                     value: rhs.value,
//                 })),
//             };
//         }

//         let body = HirNode::block(rest, &scope, body_id, &body_info, ctx)?;
//         let span = self.span.extend_to(&body.src().span.unwrap());
//         Ok(Node::new(
//             Let(
//                 vec![Node {
//                     id,
//                     info: info.clone(),
//                     value: HirDecl::var(fn_fqn.to_string(), rhs),
//                 }],
//                 Box::new(body),
//             ),
//             SourceInfo::new(Source {
//                 filepath: info.src.filepath.clone(),
//                 span: Some(span),
//             }),
//         ))
//     }
// }

// impl IntoHirNode for ast::List {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         rest: &mut VecDeque<Node<ast::Expr>,
//         scope: &Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let items = self.items.to_hir_node(scope, id, info, ctx)?;
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: List(items),
//         })
//     }
// }

// impl IntoHirNode for ast::Literal {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         _: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         _: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Literal(self.clone()),
//         })
//     }
// }

// impl IntoHirNode for ast::Name {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         _: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         log::debug!("lookup fqn: {}", self.name);
//         let fqn = if let Some(fqn) = ctx.lookup_fqn(&self.name) {
//             log::debug!("fqn for `{}`: {}", self.name, fqn);
//             fqn.clone()
//         } else {
//             Path::from(self.name.clone())
//         };

//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Var(fqn),
//         })
//     }
// }

// impl IntoHirNode for ast::Range {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node<ast::Expr>,
//         scope: &Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let start = self.start.to_hir_node(scope, id, info, ctx)?;
//         let end = self.end.to_hir_node(scope, id, info, ctx)?;
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Range(
//                 Box::new(start),
//                 Box::new(end),
//                 matches!(self.limits, ast::RangeLimits::Inclusive),
//             ),
//         })
//     }
// }

// impl IntoHirNode for ast::Sequence {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node<ast::Expr>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let els = self.items.to_hir_node(scope, id, info, ctx)?;
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Tuple(els),
//         })
//     }
// }

// impl IntoHirNode for ast::UnaryOp {
//     type Output = OutNode;

//     fn to_hir_node_with(
//         self,
//         _: &mut VecDeque<Node>,
//         scope: &ast::Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Self::Output> {
//         let expr = self.expr.to_hir_node(scope, id, info, ctx)?;
//         let name = self.op.to_string();
//         let fqn = if let Some(fqn) = ctx.lookup_fqn(&name) {
//             fqn.clone()
//         } else {
//             Path::from(name)
//         };

//         let op_var = Node::new(
//             Var(fqn),
//             SourceInfo::new(Source {
//                 span: Some(self.op_span),
//                 filepath: info.src.filepath.clone(),
//             }),
//         );
//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: Apply(Box::new(op_var), vec![expr]),
//         })
//     }
// }
