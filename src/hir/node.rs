use crate::utils::{indent, join, map_join};

use crate::typing::{
    ty::{Ty, TyVar},
    ApplySubst, Subst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedHirNode<T: Copy + Clone> {
    ex: Box<HirNode<T>>,
    ty: Ty,
}

impl<T: Copy + Clone> std::fmt::Display for TypedHirNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.ex, self.ty)
    }
}

impl<T: Copy + Clone> ApplySubst for TypedHirNode<T> {
    fn apply_subst(self, subst: &Subst) -> TypedHirNode<T> {
        TypedHirNode {
            ex: Box::new(self.ex.apply_subst(subst)),
            ty: self.ty.apply_subst(subst),
        }
    }
}

impl<T: Copy + Clone> TypedHirNode<T> {
    pub fn new(ex: HirNode<T>, ty: Ty) -> TypedHirNode<T> {
        TypedHirNode {
            ex: Box::new(ex),
            ty,
        }
    }

    pub fn get_expr(&self) -> &HirNode<T> {
        self.ex.as_ref()
    }

    pub fn get_metadata(&self) -> Option<T> {
        self.ex.as_ref().metadata
    }

    pub fn take_expr(self) -> HirNode<T> {
        *self.ex
    }

    pub fn get_type(&self) -> Ty {
        self.ty.clone()
    }

    pub fn set_type(&mut self, ty: Ty) {
        self.ty = ty;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirNode<T: Copy + Clone> {
    pub kind: HirNodeKind<T>,
    pub metadata: Option<T>,
}

impl<T: Copy + Clone> std::fmt::Display for HirNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl<T: Copy + Clone> ApplySubst for HirNode<T> {
    fn apply_subst(self, subst: &Subst) -> HirNode<T> {
        HirNode {
            kind: self.kind.apply_subst(subst),
            metadata: self.metadata,
        }
    }
}

impl<T: Copy + Clone> ApplySubst for Vec<HirNode<T>> {
    fn apply_subst(self, subst: &Subst) -> Vec<HirNode<T>> {
        self.into_iter().map(|e| e.apply_subst(subst)).collect()
    }
}

impl<T: Copy + Clone> HirNode<T> {
    pub fn new(kind: HirNodeKind<T>) -> HirNode<T> {
        HirNode {
            kind,
            metadata: None,
        }
    }
    pub fn typed(t: TypedHirNode<T>) -> HirNode<T> {
        HirNode {
            kind: HirNodeKind::Typed(t),
            metadata: None,
        }
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
pub struct Param<T> {
    name: String,
    ty: Option<Ty>,
    metadata: Option<T>,
}

impl<T: Copy + Clone> ApplySubst for Param<T> {
    fn apply_subst(self, subst: &Subst) -> Param<T> {
        let name = self.name;
        let metadata = self.metadata;
        let ty = self.ty.map(|t| t.apply_subst(subst));
        Param { name, ty, metadata }
    }
}

impl<T> std::fmt::Display for Param<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "{}: {}", self.name, ty)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl<T: Copy + Clone> Param<T> {
    pub fn new(name: String, ty: Option<Ty>) -> Param<T> {
        Param {
            name,
            ty,
            metadata: None,
        }
    }

    pub fn new_with_metadata(name: String, ty: Option<Ty>, metadata: T) -> Param<T> {
        Param {
            name,
            ty,
            metadata: Some(metadata),
        }
    }

    pub fn get_name(&self) -> &String {
        &self.name
    }

    pub fn get_ty(&self) -> Option<&Ty> {
        self.ty.as_ref()
    }

    pub fn get_ty_mut(&mut self) -> &mut Option<Ty> {
        &mut self.ty
    }

    pub fn get_metadata(&self) -> Option<T> {
        self.metadata
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirNodeKind<T: Copy + Clone> {
    Var(String),
    Const(Ty),
    Struct(String, Vec<(String, HirNode<T>)>),
    Let(Vec<(String, HirNode<T>)>, Box<HirNode<T>>),
    Fun(Vec<TyVar>, Vec<Param<T>>, Box<HirNode<T>>),
    FunInf(Vec<TyVar>, Vec<Param<T>>, Box<HirNode<T>>),
    Apply(Box<HirNode<T>>, Vec<Ty>, Vec<HirNode<T>>),
    Typed(TypedHirNode<T>),
}

impl<T: Copy + Clone> std::fmt::Display for HirNodeKind<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HirNodeKind::Var(n) => write!(f, "{}", n),
            HirNodeKind::Const(t) => write!(f, "const({})", t),
            HirNodeKind::Struct(n, els) => write!(
                f,
                "{} ({})",
                n,
                map_join(els, ", ", |(n, el)| { format!("{}: {}", n, el) })
            ),
            HirNodeKind::Apply(fun, ty_args, args) => {
                let args = join(args, ", ");
                if ty_args.len() == 0 {
                    write!(f, "{}({})", fun, args)
                } else {
                    write!(f, "{}[{}]({})", fun, join(ty_args, ", "), args)
                }
            }
            HirNodeKind::Fun(ty_vars, params, body) => write!(
                f,
                "fn{}({}) {{\n{}\n}}",
                if ty_vars.len() != 0 {
                    format!("[{}]", join(ty_vars, ", "))
                } else {
                    "".to_string()
                },
                join(params, ", "),
                indent(body.to_string(), 2)
            ),
            HirNodeKind::FunInf(ty_vars, params, body) => write!(
                f,
                "fn{}({}) {{\n{}\n}}",
                if ty_vars.len() != 0 {
                    format!("[{}]", join(ty_vars, ", "))
                } else {
                    "".to_string()
                },
                join(params, ", "),
                indent(body.to_string(), 2)
            ),
            HirNodeKind::Let(vars, b) => {
                let v = map_join(vars, ",\n", |(n, x)| format!("{} = {}", n, x));
                let lhs = if vars.len() <= 1 {
                    v
                } else {
                    format!("(\n{}\n)", indent(v, 2))
                };

                write!(f, "let {} in {{\n{}\n}}", lhs, indent(b.to_string(), 2))
            }
            HirNodeKind::Typed(e) => write!(f, "{}", e),
        }
    }
}

impl<T: Copy + Clone> ApplySubst for HirNodeKind<T> {
    fn apply_subst(self, subst: &Subst) -> HirNodeKind<T> {
        match self {
            HirNodeKind::Var(v) => HirNodeKind::Var(v),
            HirNodeKind::Const(t) => HirNodeKind::Const(t),
            HirNodeKind::Struct(n, els) => HirNodeKind::Struct(
                n,
                els.into_iter()
                    .map(|(n, el)| (n, el.apply_subst(subst)))
                    .collect(),
            ),
            HirNodeKind::Apply(fun, ty_args, args) => HirNodeKind::Apply(
                Box::new(fun.apply_subst(subst)),
                ty_args.apply_subst(subst),
                args.apply_subst(subst),
            ),
            HirNodeKind::Fun(ty_vars, params, body) => HirNodeKind::Fun(
                ty_vars,
                params.into_iter().map(|p| p.apply_subst(subst)).collect(),
                Box::new(body.apply_subst(subst)),
            ),
            HirNodeKind::FunInf(ty_vars, params, body) => {
                HirNodeKind::FunInf(ty_vars, params, Box::new(body.apply_subst(subst)))
            }
            HirNodeKind::Let(vars, b) => HirNodeKind::Let(
                vars.into_iter()
                    .map(|(n, x)| (n, x.apply_subst(subst)))
                    .collect(),
                Box::new(b.apply_subst(subst)),
            ),
            HirNodeKind::Typed(e) => HirNodeKind::Typed(e.apply_subst(subst)),
        }
    }
}

impl<T: Copy + Clone> ApplySubst for Vec<HirNodeKind<T>> {
    fn apply_subst(self, subst: &Subst) -> Vec<HirNodeKind<T>> {
        self.into_iter().map(|e| e.apply_subst(subst)).collect()
    }
}

impl<T: Copy + Clone> Into<HirNode<T>> for HirNodeKind<T> {
    fn into(self) -> HirNode<T> {
        HirNode::new(self)
    }
}
