use std::collections::VecDeque;

use crate::{
    ast::{Expr, Literal, Path},
    errors::RayResult,
    pathlib::FilePath,
    span::Source,
    typing::{top::traits::HasType, ty::Ty, ApplySubst, Ctx, Subst},
    utils::{indent, join, map_join},
};

use super::IntoHirNode;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedHirNode {
    ex: Box<HirNode>,
    ty: Ty,
}

impl std::fmt::Display for TypedHirNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.ex, self.ty)
    }
}

impl ApplySubst for TypedHirNode {
    fn apply_subst(self, subst: &Subst) -> TypedHirNode {
        TypedHirNode {
            ex: Box::new(self.ex.apply_subst(subst)),
            ty: self.ty.apply_subst(subst),
        }
    }
}

impl Into<HirNode> for TypedHirNode {
    fn into(self) -> HirNode {
        HirNodeKind::Typed(self).into()
    }
}

impl TypedHirNode {
    pub fn new(ex: HirNode, ty: Ty) -> TypedHirNode {
        TypedHirNode {
            ex: Box::new(ex),
            ty,
        }
    }

    pub fn get_expr(&self) -> &HirNode {
        self.ex.as_ref()
    }

    pub fn get_src(&self) -> Option<&Source> {
        self.ex.src.as_ref()
    }

    pub fn take_expr(self) -> HirNode {
        *self.ex
    }

    pub fn take(self) -> (HirNode, Ty) {
        (*self.ex, self.ty)
    }

    pub fn get_type(&self) -> Ty {
        self.ty.clone()
    }

    pub fn set_type(&mut self, ty: Ty) {
        self.ty = ty;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirNode {
    pub kind: HirNodeKind,
    pub src: Option<Source>,
}

impl std::fmt::Display for HirNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl ApplySubst for HirNode {
    fn apply_subst(self, subst: &Subst) -> HirNode {
        HirNode {
            kind: self.kind.apply_subst(subst),
            src: self.src,
        }
    }
}

impl HasType for HirNode {
    fn get_type(&self) -> Ty {
        match &self.kind {
            HirNodeKind::Typed(t) => t.get_type(),
            _ => Ty::unit(),
        }
    }
}

impl HirNode {
    pub fn new(kind: HirNodeKind) -> HirNode {
        HirNode { kind, src: None }
    }

    pub fn typed(t: TypedHirNode) -> HirNode {
        HirNode {
            kind: HirNodeKind::Typed(t),
            src: None,
        }
    }

    pub fn block(
        exprs: &mut VecDeque<Expr>,
        scope: &Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> RayResult<HirNode> {
        let mut nodes = vec![];
        while let Some(first) = exprs.pop_front() {
            nodes.push(first.to_hir_node_with(exprs, scope, filepath, ctx)?);
        }

        Ok(if nodes.len() != 0 {
            HirNodeKind::Block(nodes).into()
        } else {
            // otherwise it'll be a const unit
            HirNodeKind::Literal(Literal::Unit).into()
        })
    }

    pub fn get_type(&self) -> Ty {
        if let HirNodeKind::Typed(t) = &self.kind {
            t.get_type()
        } else {
            panic!("not a typed expression: {}", self)
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
pub enum HirDeclKind {
    Pattern(HirPattern, Box<HirNode>),
    Type(String, Ty),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirDecl {
    pub kind: HirDeclKind,
    pub src: Option<Source>,
}

impl HirDecl {
    pub fn var<S: Into<String>, R: Into<HirNode>>(var: S, rhs: R) -> HirDecl {
        HirDecl {
            kind: HirDeclKind::Pattern(HirPattern::Var(var.into()), Box::new(rhs.into())),
            src: None,
        }
    }

    pub fn ty<S: Into<String>>(name: S, ty: Ty) -> HirDecl {
        HirDecl {
            kind: HirDeclKind::Type(name.into(), ty),
            src: None,
        }
    }

    pub fn with_src(mut self, src: Option<Source>) -> HirDecl {
        self.src = src;
        self
    }
}

impl std::fmt::Display for HirDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            HirDeclKind::Pattern(x, n) => write!(f, "{} = {}", x, n),
            HirDeclKind::Type(x, t) => write!(f, "{} :: {}", x, t),
        }
    }
}

impl ApplySubst for HirDecl {
    fn apply_subst(self, subst: &Subst) -> HirDecl {
        let span = self.src;
        let kind = match self.kind {
            HirDeclKind::Pattern(x, n) => HirDeclKind::Pattern(x, Box::new(n.apply_subst(subst))),
            HirDeclKind::Type(x, t) => HirDeclKind::Type(x, t.apply_subst(subst)),
        };
        HirDecl { kind, src: span }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirNodeKind {
    Var(String),
    Literal(Literal),
    Type(Ty),
    Cast(Box<HirNode>, Ty),
    Decl(HirDecl),
    Struct(String, Vec<(String, HirNode)>),
    Block(Vec<HirNode>),
    Let(Vec<HirDecl>, Box<HirNode>),
    Fun(Vec<Param>, Box<HirNode>),
    Apply(Box<HirNode>, Vec<HirNode>),
    Typed(TypedHirNode),
}

impl std::fmt::Display for HirNodeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirNodeKind::Var(n) => write!(f, "{}", n),
            HirNodeKind::Literal(l) => write!(f, "{}", l),
            HirNodeKind::Type(t) => write!(f, "{}", t),
            HirNodeKind::Cast(b, t) => write!(f, "({} as {})", b, t),
            HirNodeKind::Decl(d) => write!(f, "{}", d),
            HirNodeKind::Struct(n, els) => write!(
                f,
                "{} ({})",
                n,
                map_join(els, ", ", |(n, el)| { format!("{}: {}", n, el) })
            ),
            HirNodeKind::Apply(fun, args) => {
                let args = join(args, ", ");
                write!(f, "{}({})", fun, args)
            }
            HirNodeKind::Fun(params, body) => write!(
                f,
                "fn({}) {{\n{}\n}}",
                join(params, ", "),
                indent(body.to_string(), 2)
            ),
            HirNodeKind::Let(decls, b) => {
                let v = map_join(decls, ",\n", |d| d.to_string());
                let lhs = if decls.len() <= 1 {
                    v
                } else {
                    format!("(\n{}\n)", indent(v, 2))
                };

                let body = if matches!(b.kind, HirNodeKind::Block(_)) {
                    b.to_string()
                } else {
                    format!("{{\n{}\n}}", indent(b.to_string(), 2))
                };

                write!(f, "let {} in {}", lhs, body)
            }
            HirNodeKind::Block(b) => {
                if b.len() == 0 {
                    write!(f, "()")
                } else if b.len() == 1 {
                    write!(f, "{{ {} }}", join(b, ", "))
                } else {
                    write!(f, "{{\n{}\n}}", indent(join(b, "\n"), 2))
                }
            }
            HirNodeKind::Typed(e) => write!(f, "{}", e),
        }
    }
}

impl ApplySubst for HirNodeKind {
    fn apply_subst(self, subst: &Subst) -> HirNodeKind {
        match self {
            HirNodeKind::Var(v) => HirNodeKind::Var(v),
            HirNodeKind::Type(ty) => HirNodeKind::Type(ty.apply_subst(subst)),
            HirNodeKind::Literal(l) => HirNodeKind::Literal(l),
            HirNodeKind::Cast(d, t) => {
                HirNodeKind::Cast(Box::new(d.apply_subst(subst)), t.apply_subst(subst))
            }
            HirNodeKind::Decl(d) => HirNodeKind::Decl(d.apply_subst(subst)),
            HirNodeKind::Struct(n, els) => HirNodeKind::Struct(
                n,
                els.into_iter()
                    .map(|(n, el)| (n, el.apply_subst(subst)))
                    .collect(),
            ),
            HirNodeKind::Apply(fun, args) => {
                HirNodeKind::Apply(Box::new(fun.apply_subst(subst)), args.apply_subst(subst))
            }
            HirNodeKind::Fun(params, body) => HirNodeKind::Fun(
                params.into_iter().map(|p| p.apply_subst(subst)).collect(),
                Box::new(body.apply_subst(subst)),
            ),
            HirNodeKind::Let(vars, b) => HirNodeKind::Let(
                vars.into_iter().map(|d| d.apply_subst(subst)).collect(),
                Box::new(b.apply_subst(subst)),
            ),
            HirNodeKind::Block(b) => HirNodeKind::Block(b.apply_subst(subst)),
            HirNodeKind::Typed(e) => HirNodeKind::Typed(e.apply_subst(subst)),
        }
    }
}

impl Into<HirNode> for HirNodeKind {
    fn into(self) -> HirNode {
        HirNode::new(self)
    }
}
