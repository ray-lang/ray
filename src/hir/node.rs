// use std::collections::VecDeque;

// use crate::{
//     ast::{
//         asm::{AsmOp, AsmOperand},
//         Decorator, Expr, Literal, Node, Path, SourceInfo,
//     },
//     errors::RayResult,
//     span::Source,
//     typing::{traits::HasType, ty::Ty, ApplySubst, Subst, TyCtx},
//     utils::{indent, join, map_join},
// };

// use super::{HirInfo, IntoHirNode};

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct HirField(String);

// impl std::fmt::Display for HirField {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}", self.0)
//     }
// }

// impl HirField {
//     pub fn new<S: ToString>(name: S) -> HirField {
//         HirField(name.to_string())
//     }

//     pub fn name(&self) -> &String {
//         &self.0
//     }
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum HirNode
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     Var(Path),
//     Literal(Literal),
//     Range(
//         Box<Node<HirNode>,
//         Box<Node<HirNode>,
//         bool,
//     ),
//     Tuple(Vec<Node<HirNode>),
//     List(Vec<Node<HirNode>),
//     Type(Ty),
//     Asm(Option<Ty>, Vec<(AsmOp, Vec<AsmOperand>)>),
//     Cast(Box<Node<HirNode>, Ty),
//     Decl(Node<HirDecl>),
//     Struct(Path, Ty, Vec<(String, Node<HirNode>),
//     Block(Vec<Node<HirNode>),
//     Dot(Box<Node<HirNode, Info>>, Node<HirField>),
//     DerefAssign(
//         Box<Node<HirNode>,
//         Box<Node<HirNode>,
//     ),
//     Let(
//         Vec<Node<HirDecl>,
//         Box<Node<HirNode>,
//     ),
//     Fn(
//         Vec<Param>,
//         Box<Node<HirNode>,
//         Option<Vec<Decorator>>,
//     ),
//     Apply(
//         Box<Node<HirNode>,
//         Vec<Node<HirNode>,
//     ),
//     Typed(Box<Node<HirNode>),
// }

// impl std::fmt::Display for HirNode
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             HirNode::Var(n) => write!(f, "{}", n),
//             HirNode::Range(start, end, is_inclusive) => {
//                 if *is_inclusive {
//                     write!(f, "{}..={}", start, end)
//                 } else {
//                     write!(f, "{}..<{}", start, end)
//                 }
//             }
//             HirNode::Literal(l) => write!(f, "{}", l),
//             HirNode::Type(t) => write!(f, "{}", t),
//             HirNode::List(t) => write!(f, "[{}]", join(t, ", ")),
//             HirNode::Tuple(t) => write!(f, "({})", join(t, ", ")),
//             HirNode::Asm(ret_ty, inst) => {
//                 write!(
//                     f,
//                     "asm{} {{\n{}\n}}",
//                     ret_ty
//                         .as_ref()
//                         .map(|r| format!("({})", r))
//                         .unwrap_or_default(),
//                     indent(
//                         map_join(inst, "\n", |(op, operands)| {
//                             format!("{} {}", op, join(operands, " "))
//                         }),
//                         2
//                     )
//                 )
//             }
//             HirNode::Cast(b, t) => write!(f, "({} as {})", b, t),
//             HirNode::Decl(d) => write!(f, "{}", d),
//             HirNode::Struct(fqn, _, els) => write!(
//                 f,
//                 "{} ({})",
//                 fqn,
//                 map_join(els, ", ", |(n, el)| { format!("{}: {}", n, el) })
//             ),
//             HirNode::Dot(lhs, name) => {
//                 write!(f, "{}.{}", lhs, name)
//             }
//             HirNode::Apply(fun, args) => {
//                 let args = join(args, ", ");
//                 write!(f, "{}({})", fun, args)
//             }
//             HirNode::Fn(params, body, decs) => write!(
//                 f,
//                 "{}fn({}) {{\n{}\n}}",
//                 decs.as_ref()
//                     .map(|d| { format!("{}\n", join(d, "\n")) })
//                     .unwrap_or_default(),
//                 join(params, ", "),
//                 indent(body.to_string(), 2)
//             ),
//             HirNode::DerefAssign(lhs, rhs) => {
//                 write!(f, "*{} = {}", lhs, rhs)
//             }
//             HirNode::Let(decls, b) => {
//                 let v = map_join(decls, ",\n", |d| d.to_string());
//                 let lhs = if decls.len() <= 1 {
//                     v
//                 } else {
//                     format!("(\n{}\n)", indent(v, 2))
//                 };

//                 let body = if matches!(b.value, HirNode::Block(_)) {
//                     b.to_string()
//                 } else {
//                     format!("{{\n{}\n}}", indent(b.to_string(), 2))
//                 };

//                 write!(f, "let {} in {}", lhs, body)
//             }
//             HirNode::Block(b) => {
//                 if b.len() == 0 {
//                     write!(f, "()")
//                 } else if b.len() == 1 {
//                     write!(f, "{{ {} }}", join(b, ", "))
//                 } else {
//                     write!(f, "{{\n{}\n}}", indent(join(b, "\n"), 2))
//                 }
//             }
//             HirNode::Typed(e) => write!(f, "{}", e),
//         }
//     }
// }

// impl ApplySubst for HirNode
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
// {
//     fn apply_subst(self, subst: &Subst) -> HirNode {
//         match self {
//             HirNode::Var(v) => HirNode::Var(v.apply_subst(subst)),
//             HirNode::Type(ty) => HirNode::Type(ty.apply_subst(subst)),
//             HirNode::Range(start, end, is_inc) => {
//                 HirNode::Range(start.apply_subst(subst), end.apply_subst(subst), is_inc)
//             }
//             HirNode::Literal(l) => HirNode::Literal(l),
//             HirNode::List(t) => HirNode::List(t.apply_subst(subst)),
//             HirNode::Tuple(t) => HirNode::Tuple(t.apply_subst(subst)),
//             HirNode::Asm(ty, inst) => HirNode::Asm(ty.map(|t| t.apply_subst(subst)), inst),
//             HirNode::Cast(d, t) => HirNode::Cast(d.apply_subst(subst), t.apply_subst(subst)),
//             HirNode::Decl(d) => HirNode::Decl(d.apply_subst(subst)),
//             HirNode::Struct(fqn, ty, els) => {
//                 HirNode::Struct(fqn, ty.apply_subst(subst), els.apply_subst(subst))
//             }
//             HirNode::Dot(lhs, n) => HirNode::Dot(lhs.apply_subst(subst), n),
//             HirNode::Apply(fun, args) => {
//                 HirNode::Apply(fun.apply_subst(subst), args.apply_subst(subst))
//             }
//             HirNode::Fn(params, body, dec) => HirNode::Fn(
//                 params.into_iter().map(|p| p.apply_subst(subst)).collect(),
//                 body.apply_subst(subst),
//                 dec,
//             ),
//             HirNode::DerefAssign(lhs, rhs) => {
//                 HirNode::DerefAssign(lhs.apply_subst(subst), rhs.apply_subst(subst))
//             }
//             HirNode::Let(vars, b) => HirNode::Let(
//                 vars.into_iter().map(|d| d.apply_subst(subst)).collect(),
//                 b.apply_subst(subst),
//             ),
//             HirNode::Block(b) => HirNode::Block(b.apply_subst(subst)),
//             HirNode::Typed(e) => HirNode::Typed(e.apply_subst(subst)),
//         }
//     }
// }

// // #[derive(Clone, Debug, PartialEq, Eq)]
// // pub struct TypedHirNode
// // where
// //     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// // {
// //     ex: Box<HirNode>,
// //     ty: Ty,
// // }

// // impl std::fmt::Display for TypedHirNode
// // where
// //     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// // {
// //     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
// //         write!(f, "{} : {}", self.ex, self.ty)
// //     }
// // }

// // impl ApplySubst for TypedHirNode
// // where
// //     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// // {
// //     fn apply_subst(self, subst: &Subst) -> TypedHirNode {
// //         TypedHirNode {
// //             ex: Box::new(self.ex.apply_subst(subst)),
// //             ty: self.ty.apply_subst(subst),
// //         }
// //     }
// // }

// // impl Into<HirNode> for TypedHirNode
// // where
// //     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// // {
// //     fn into(self) -> HirNode {
// //         HirNode::Typed(self)
// //     }
// // }

// // impl TypedHirNode
// // where
// //     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// // {
// //     pub fn new(ex: HirNode, ty: Ty) -> TypedHirNode {
// //         TypedHirNode {
// //             ex: Box::new(ex),
// //             ty,
// //         }
// //     }

// //     pub fn get_expr(&self) -> &HirNode {
// //         self.ex.as_ref()
// //     }

// //     pub fn get_src(&self) -> Option<&Source> {
// //         self.ex.src.as_ref()
// //     }

// //     pub fn take_expr(self) -> HirNode {
// //         *self.ex
// //     }

// //     pub fn take(self) -> (HirNode, Ty) {
// //         (*self.ex, self.ty)
// //     }

// //     pub fn get_type(&self) -> Ty {
// //         self.ty.clone()
// //     }

// //     pub fn set_type(&mut self, ty: Ty) {
// //         self.ty = ty;
// //     }
// // }

// impl HasType for HirNode
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn ty(&self) -> Ty {
//         match &self {
//             HirNode::Typed(t) => t.ty(),
//             _ => Ty::unit(),
//         }
//     }
// }

// impl HirNode {
//     pub fn block(
//         exprs: &mut VecDeque<Node<Expr>,
//         scope: &Path,
//         id: u64,
//         info: &SourceInfo,
//         ctx: &mut TyCtx,
//     ) -> RayResult<Node<HirNode> {
//         let mut nodes = vec![];
//         while let Some(first) = exprs.pop_front() {
//             nodes.push(first.to_hir_node_with(exprs, scope, id, info, ctx)?);
//         }

//         Ok(Node {
//             id,
//             info: info.clone(),
//             value: if nodes.len() != 0 {
//                 HirNode::Block(nodes)
//             } else {
//                 // otherwise it'll be a const unit
//                 HirNode::Literal(Literal::Unit)
//             },
//         })
//     }
// }

// impl HirNode
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     pub fn name(&self) -> Option<Path> {
//         match &self {
//             HirNode::Var(v) => Some(v.clone()),
//             HirNode::Typed(t) => t.value.name(),
//             _ => None,
//         }
//     }

//     pub fn borrow_typed(&self) -> Option<(&HirNode, Ty)> {
//         if let HirNode::Typed(t) = &self {
//             Some((&t.value, t.ty()))
//         } else {
//             None
//         }
//     }
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct Param {
//     name: String,
//     ty: Option<Ty>,
//     span: Option<Source>,
// }

// impl ApplySubst for Param {
//     fn apply_subst(self, subst: &Subst) -> Param {
//         let name = self.name;
//         let span = self.span;
//         let ty = self.ty.map(|t| t.apply_subst(subst));
//         Param { name, ty, span }
//     }
// }

// impl std::fmt::Display for Param {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         if let Some(ty) = &self.ty {
//             write!(f, "{}: {}", self.name, ty)
//         } else {
//             write!(f, "{}", self.name)
//         }
//     }
// }

// impl Param {
//     pub fn new(name: String, ty: Option<Ty>) -> Param {
//         Param {
//             name,
//             ty,
//             span: None,
//         }
//     }

//     pub fn get_name(&self) -> &String {
//         &self.name
//     }

//     pub fn get_ty(&self) -> Option<&Ty> {
//         self.ty.as_ref()
//     }

//     pub fn set_ty(&mut self, ty: Ty) {
//         self.ty = Some(ty)
//     }

//     pub fn get_ty_mut(&mut self) -> &mut Option<Ty> {
//         &mut self.ty
//     }

//     pub fn get_span(&self) -> Option<&Source> {
//         self.span.as_ref()
//     }
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum HirPattern {
//     Var(Path),
// }

// impl std::fmt::Display for HirPattern {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             HirPattern::Var(x) => write!(f, "{}", x),
//         }
//     }
// }

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub enum HirDecl
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     Pattern(HirPattern, Box<Node<HirNode>),
//     Extern(Path, Ty, bool, Option<String>),
//     Type(Path, Ty, bool, Option<String>),
//     Fn(
//         Path,
//         Vec<Param>,
//         Box<Node<HirNode>,
//         Option<Vec<Decorator>>,
//     ),
//     TraitMember(Path, Ty),
// }

// impl HirDecl
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     pub fn var<P: Into<Path>>(var: P, rhs: Node<HirNode> {
//         HirDecl::Pattern(HirPattern::Var(var.into()), Box::new(rhs))
//     }

//     pub fn member<P: Into<Path>>(name: P, ty: Ty) -> HirDecl {
//         HirDecl::TraitMember(name.into(), ty)
//     }
// }

// impl std::fmt::Display for HirDecl
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match &self {
//             HirDecl::Pattern(x, n) => write!(f, "{} = {}", x, n),
//             HirDecl::Fn(x, params, body, _) => {
//                 write!(
//                     f,
//                     "fn {}({}) {{\n{}\n}}",
//                     x,
//                     join(params, ", "),
//                     indent(body.to_string(), 2)
//                 )
//             }
//             HirDecl::Extern(x, t, _, _)
//             | HirDecl::Type(x, t, _, _)
//             | HirDecl::TraitMember(x, t) => write!(f, "{} :: {}", x, t),
//         }
//     }
// }

// impl ApplySubst for HirDecl
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
// {
//     fn apply_subst(self, subst: &Subst) -> HirDecl {
//         match self {
//             HirDecl::Pattern(x, n) => HirDecl::Pattern(x, n.apply_subst(subst)),
//             HirDecl::Type(x, t, is_mutable, src) => {
//                 HirDecl::Type(x, t.apply_subst(subst), is_mutable, src)
//             }
//             HirDecl::Extern(x, t, is_mutable, src) => {
//                 HirDecl::Extern(x, t.apply_subst(subst), is_mutable, src)
//             }
//             HirDecl::Fn(name, params, body, decs) => HirDecl::Fn(
//                 name,
//                 params.apply_subst(subst),
//                 body.apply_subst(subst),
//                 decs,
//             ),
//             HirDecl::TraitMember(x, t) => HirDecl::TraitMember(x, t.apply_subst(subst)),
//         }
//     }
// }
