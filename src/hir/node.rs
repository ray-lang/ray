use std::collections::VecDeque;

use crate::{
    ast::{asm::AsmOp, Decorator, Expr, Literal, Node, Path, SourceInfo},
    errors::RayResult,
    span::Source,
    typing::{traits::HasType, ty::Ty, ApplySubst, Ctx, Subst},
    utils::{indent, join, map_join},
};

use super::{HirInfo, IntoHirNode};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirField(String);

impl std::fmt::Display for HirField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl HirField {
    pub fn new<S: ToString>(name: S) -> HirField {
        HirField(name.to_string())
    }

    pub fn name(&self) -> &String {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirNode<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Var(String),
    Literal(Literal),
    Tuple(Vec<Node<HirNode<Info>, Info>>),
    Type(Ty),
    Asm(Option<Ty>, Vec<(AsmOp, Vec<String>)>),
    Cast(Box<Node<HirNode<Info>, Info>>, Ty),
    Decl(Node<HirDecl<Info>, Info>),
    Struct(Path, Ty, Vec<(String, Node<HirNode<Info>, Info>)>),
    Block(Vec<Node<HirNode<Info>, Info>>),
    Dot(Box<Node<HirNode<Info>, Info>>, Node<HirField, Info>),
    Let(
        Vec<Node<HirDecl<Info>, Info>>,
        Box<Node<HirNode<Info>, Info>>,
    ),
    Fun(
        Vec<Param>,
        Box<Node<HirNode<Info>, Info>>,
        Option<Vec<Decorator>>,
    ),
    Apply(
        Box<Node<HirNode<Info>, Info>>,
        Vec<Node<HirNode<Info>, Info>>,
    ),
    Typed(Box<Node<HirNode<Info>, HirInfo>>),
}

impl<Info> std::fmt::Display for HirNode<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirNode::Var(n) => write!(f, "{}", n),
            HirNode::Literal(l) => write!(f, "{}", l),
            HirNode::Type(t) => write!(f, "{}", t),
            HirNode::Tuple(t) => write!(f, "({})", join(t, ", ")),
            HirNode::Asm(ret_ty, inst) => {
                write!(
                    f,
                    "asm{} {{\n{}\n}}",
                    ret_ty
                        .as_ref()
                        .map(|r| format!("({})", r))
                        .unwrap_or_default(),
                    indent(
                        map_join(inst, "\n", |(op, operands)| {
                            format!("{} {}", op, join(operands, " "))
                        }),
                        2
                    )
                )
            }
            HirNode::Cast(b, t) => write!(f, "({} as {})", b, t),
            HirNode::Decl(d) => write!(f, "{}", d),
            HirNode::Struct(fqn, _, els) => write!(
                f,
                "{} ({})",
                fqn,
                map_join(els, ", ", |(n, el)| { format!("{}: {}", n, el) })
            ),
            HirNode::Dot(lhs, name) => {
                write!(f, "{}.{}", lhs, name)
            }
            HirNode::Apply(fun, args) => {
                let args = join(args, ", ");
                write!(f, "{}({})", fun, args)
            }
            HirNode::Fun(params, body, decs) => write!(
                f,
                "{}fn({}) {{\n{}\n}}",
                decs.as_ref()
                    .map(|d| { format!("{}\n", join(d, "\n")) })
                    .unwrap_or_default(),
                join(params, ", "),
                indent(body.to_string(), 2)
            ),
            HirNode::Let(decls, b) => {
                let v = map_join(decls, ",\n", |d| d.to_string());
                let lhs = if decls.len() <= 1 {
                    v
                } else {
                    format!("(\n{}\n)", indent(v, 2))
                };

                let body = if matches!(b.value, HirNode::Block(_)) {
                    b.to_string()
                } else {
                    format!("{{\n{}\n}}", indent(b.to_string(), 2))
                };

                write!(f, "let {} in {}", lhs, body)
            }
            HirNode::Block(b) => {
                if b.len() == 0 {
                    write!(f, "()")
                } else if b.len() == 1 {
                    write!(f, "{{ {} }}", join(b, ", "))
                } else {
                    write!(f, "{{\n{}\n}}", indent(join(b, "\n"), 2))
                }
            }
            HirNode::Typed(e) => write!(f, "{}", e),
        }
    }
}

impl<Info> ApplySubst for HirNode<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> HirNode<Info> {
        match self {
            HirNode::Var(v) => HirNode::Var(v),
            HirNode::Type(ty) => HirNode::Type(ty.apply_subst(subst)),
            HirNode::Literal(l) => HirNode::Literal(l),
            HirNode::Tuple(t) => HirNode::Tuple(t.apply_subst(subst)),
            HirNode::Asm(ty, inst) => HirNode::Asm(ty.map(|t| t.apply_subst(subst)), inst),
            HirNode::Cast(d, t) => HirNode::Cast(d.apply_subst(subst), t.apply_subst(subst)),
            HirNode::Decl(d) => HirNode::Decl(d.apply_subst(subst)),
            HirNode::Struct(fqn, ty, els) => {
                HirNode::Struct(fqn, ty.apply_subst(subst), els.apply_subst(subst))
            }
            HirNode::Dot(lhs, n) => HirNode::Dot(lhs.apply_subst(subst), n),
            HirNode::Apply(fun, args) => {
                HirNode::Apply(fun.apply_subst(subst), args.apply_subst(subst))
            }
            HirNode::Fun(params, body, dec) => HirNode::Fun(
                params.into_iter().map(|p| p.apply_subst(subst)).collect(),
                body.apply_subst(subst),
                dec,
            ),
            HirNode::Let(vars, b) => HirNode::Let(
                vars.into_iter().map(|d| d.apply_subst(subst)).collect(),
                b.apply_subst(subst),
            ),
            HirNode::Block(b) => HirNode::Block(b.apply_subst(subst)),
            HirNode::Typed(e) => HirNode::Typed(e.apply_subst(subst)),
        }
    }
}

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct TypedHirNode<Info>
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     ex: Box<HirNode<Info>>,
//     ty: Ty,
// }

// impl<Info> std::fmt::Display for TypedHirNode<Info>
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{} : {}", self.ex, self.ty)
//     }
// }

// impl<Info> ApplySubst for TypedHirNode<Info>
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn apply_subst(self, subst: &Subst) -> TypedHirNode<Info> {
//         TypedHirNode {
//             ex: Box::new(self.ex.apply_subst(subst)),
//             ty: self.ty.apply_subst(subst),
//         }
//     }
// }

// impl<Info> Into<HirNode<Info>> for TypedHirNode<Info>
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     fn into(self) -> HirNode<Info> {
//         HirNode::Typed(self)
//     }
// }

// impl<Info> TypedHirNode<Info>
// where
//     Info: std::fmt::Debug + Clone + PartialEq + Eq,
// {
//     pub fn new(ex: HirNode<Info>, ty: Ty) -> TypedHirNode<Info> {
//         TypedHirNode {
//             ex: Box::new(ex),
//             ty,
//         }
//     }

//     pub fn get_expr(&self) -> &HirNode<Info> {
//         self.ex.as_ref()
//     }

//     pub fn get_src(&self) -> Option<&Source> {
//         self.ex.src.as_ref()
//     }

//     pub fn take_expr(self) -> HirNode<Info> {
//         *self.ex
//     }

//     pub fn take(self) -> (HirNode<Info>, Ty) {
//         (*self.ex, self.ty)
//     }

//     pub fn get_type(&self) -> Ty {
//         self.ty.clone()
//     }

//     pub fn set_type(&mut self, ty: Ty) {
//         self.ty = ty;
//     }
// }

impl<Info> HasType for HirNode<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn ty(&self) -> Ty {
        match &self {
            HirNode::Typed(t) => t.ty(),
            _ => Ty::unit(),
        }
    }
}

impl HirNode<SourceInfo> {
    pub fn block(
        exprs: &mut VecDeque<Node<Expr<SourceInfo>, SourceInfo>>,
        scope: &Path,
        id: u64,
        info: &SourceInfo,
        ctx: &mut Ctx,
    ) -> RayResult<Node<HirNode<SourceInfo>, SourceInfo>> {
        let mut nodes = vec![];
        while let Some(first) = exprs.pop_front() {
            nodes.push(first.to_hir_node_with(exprs, scope, id, info, ctx)?);
        }

        Ok(Node {
            id,
            info: info.clone(),
            value: if nodes.len() != 0 {
                HirNode::Block(nodes)
            } else {
                // otherwise it'll be a const unit
                HirNode::Literal(Literal::Unit)
            },
        })
    }
}

impl<Info> HirNode<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn fn_name(&self) -> Option<&String> {
        match &self {
            HirNode::Var(v) => Some(v),
            HirNode::Apply(f, _) => f.fn_name(),
            HirNode::Typed(t) => t.value.fn_name(),
            _ => None,
        }
    }

    pub fn borrow_typed(&self) -> Option<(&HirNode<Info>, Ty)> {
        if let HirNode::Typed(t) = &self {
            Some((&t.value, t.ty()))
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    name: String,
    ty: Option<Ty>,
    span: Option<Source>,
}

impl ApplySubst for Param {
    fn apply_subst(self, subst: &Subst) -> Param {
        let name = self.name;
        let span = self.span;
        let ty = self.ty.map(|t| t.apply_subst(subst));
        Param { name, ty, span }
    }
}

impl std::fmt::Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "{}: {}", self.name, ty)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl Param {
    pub fn new(name: String, ty: Option<Ty>) -> Param {
        Param {
            name,
            ty,
            span: None,
        }
    }

    pub fn get_name(&self) -> &String {
        &self.name
    }

    pub fn get_ty(&self) -> Option<&Ty> {
        self.ty.as_ref()
    }

    pub fn set_ty(&mut self, ty: Ty) {
        self.ty = Some(ty)
    }

    pub fn get_ty_mut(&mut self) -> &mut Option<Ty> {
        &mut self.ty
    }

    pub fn get_span(&self) -> Option<&Source> {
        self.span.as_ref()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirPattern {
    Var(String),
}

impl std::fmt::Display for HirPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirPattern::Var(x) => write!(f, "{}", x),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirDecl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Pattern(HirPattern, Box<Node<HirNode<Info>, Info>>),
    Type(String, Ty, bool, Option<String>),
    TraitMember(String, Ty),
}

impl<Info> HirDecl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn var<S: Into<String>>(var: S, rhs: Node<HirNode<Info>, Info>) -> HirDecl<Info> {
        HirDecl::Pattern(HirPattern::Var(var.into()), Box::new(rhs))
    }

    pub fn ty<S: Into<String>>(
        name: S,
        ty: Ty,
        is_mutable: bool,
        src: Option<&str>,
    ) -> HirDecl<Info> {
        HirDecl::Type(name.into(), ty, is_mutable, src.map(|s| s.to_string()))
    }

    pub fn member<S: Into<String>>(name: S, ty: Ty) -> HirDecl<Info> {
        HirDecl::TraitMember(name.into(), ty)
    }
}

impl<Info> std::fmt::Display for HirDecl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            HirDecl::Pattern(x, n) => write!(f, "{} = {}", x, n),
            HirDecl::Type(x, t, _, _) | HirDecl::TraitMember(x, t) => write!(f, "{} :: {}", x, t),
        }
    }
}

impl<Info> ApplySubst for HirDecl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq + ApplySubst,
{
    fn apply_subst(self, subst: &Subst) -> HirDecl<Info> {
        match self {
            HirDecl::Pattern(x, n) => HirDecl::Pattern(x, n.apply_subst(subst)),
            HirDecl::Type(x, t, is_mutable, src) => {
                HirDecl::Type(x, t.apply_subst(subst), is_mutable, src)
            }
            HirDecl::TraitMember(x, t) => HirDecl::TraitMember(x, t.apply_subst(subst)),
        }
    }
}
