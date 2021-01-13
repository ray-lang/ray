use crate::ast;
use crate::span::Span;

use std::fmt;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum IntTy {
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    UInt,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntTy::Int => write!(f, "int"),
            IntTy::Int8 => write!(f, "i8"),
            IntTy::Int16 => write!(f, "i16"),
            IntTy::Int32 => write!(f, "i32"),
            IntTy::Int64 => write!(f, "i64"),
            IntTy::Int128 => write!(f, "i128"),
            IntTy::UInt => write!(f, "uint"),
            IntTy::UInt8 => write!(f, "u8"),
            IntTy::UInt16 => write!(f, "u16"),
            IntTy::UInt32 => write!(f, "u32"),
            IntTy::UInt64 => write!(f, "u64"),
            IntTy::UInt128 => write!(f, "u128"),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum FloatTy {
    Float32,
    Float64,
    Float128,
}

impl fmt::Display for FloatTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FloatTy::Float32 => write!(f, "f32"),
            FloatTy::Float64 => write!(f, "f64"),
            FloatTy::Float128 => write!(f, "f128"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeKind {
    Unknown,
    Basic {
        name: String,
        ty_params: Option<TypeParams>,
        bounds: Option<Box<Type>>,
    },
    Struct {
        name: String,
        ty_params: Option<TypeParams>,
        fields: Option<Vec<(String, Type)>>,
    },
    Fn {
        ty_params: Option<TypeParams>,
        params: Box<Type>,
        ret: Option<Box<Type>>,
    },
    Generic(String),
    Pointer(Box<Type>),
    Bool,
    Char,
    String,
    Nil,
    Int(IntTy), // size, signed
    Float(FloatTy),
    List(Box<Type>),
    Sequence(Vec<Type>),
    Array(Box<Type>, usize),
    TypeVar(usize),
    Union(Vec<Type>),
}

impl TypeKind {
    pub fn unit() -> TypeKind {
        TypeKind::Sequence(vec![])
    }

    pub fn from_str(s: &str) -> Option<TypeKind> {
        Some(match s {
            "int" => TypeKind::Int(IntTy::Int),
            "i8" => TypeKind::Int(IntTy::Int8),
            "i16" => TypeKind::Int(IntTy::Int16),
            "i32" => TypeKind::Int(IntTy::Int32),
            "i64" => TypeKind::Int(IntTy::Int64),
            "i128" => TypeKind::Int(IntTy::Int128),
            "uint" => TypeKind::Int(IntTy::UInt),
            "u8" => TypeKind::Int(IntTy::UInt8),
            "u16" => TypeKind::Int(IntTy::UInt16),
            "u32" => TypeKind::Int(IntTy::UInt32),
            "u64" => TypeKind::Int(IntTy::UInt64),
            "u128" => TypeKind::Int(IntTy::UInt128),
            "float" => TypeKind::Float(FloatTy::Float32),
            "f32" => TypeKind::Float(FloatTy::Float32),
            "f64" => TypeKind::Float(FloatTy::Float64),
            "f128" => TypeKind::Float(FloatTy::Float128),
            "string" => TypeKind::String,
            "char" => TypeKind::Char,
            "bool" => TypeKind::Bool,
            "List" => TypeKind::List(Box::new(Type::new(TypeKind::Nil))),
            _ => return None,
        })
    }

    pub fn basic(name: &str) -> TypeKind {
        TypeKind::Basic {
            name: name.to_string(),
            ty_params: None,
            bounds: None,
        }
    }

    pub fn optional(ty: Type) -> TypeKind {
        TypeKind::Union(vec![ty, Type::new(TypeKind::Nil)])
    }

    pub fn pointer(ty: Type) -> TypeKind {
        TypeKind::Pointer(Box::new(ty))
    }

    pub fn anon_struct(fields: Vec<(String, Type)>) -> TypeKind {
        TypeKind::Struct {
            name: "".to_string(),
            ty_params: None,
            fields: Some(fields),
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, TypeKind::Sequence(seq) if seq.len() == 0)
    }

    pub fn is_ty_var(&self) -> bool {
        matches!(self, TypeKind::TypeVar(_))
    }

    pub fn is_generic(&self) -> bool {
        matches!(self, TypeKind::Generic { .. })
    }

    pub fn get_elements(&self) -> &Vec<Type> {
        match self {
            TypeKind::Sequence(tys) | TypeKind::Union(tys) => tys,
            _ => unreachable!(),
        }
    }

    pub fn get_elements_mut(&mut self) -> &mut Vec<Type> {
        match self {
            TypeKind::Sequence(tys) | TypeKind::Union(tys) => tys,
            _ => unreachable!(),
        }
    }
}

impl fmt::Display for TypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeKind::Unknown => write!(f, "?"),
            TypeKind::TypeVar(i) => write!(f, "?T{}", i),
            TypeKind::Basic {
                name,
                ty_params,
                bounds,
            } => write!(
                f,
                "{}{}{}",
                name,
                if let Some(ty_params) = ty_params {
                    ty_params.to_string()
                } else {
                    "".to_string()
                },
                if let Some(bounds) = bounds {
                    format!(": {}", bounds)
                } else {
                    "".to_string()
                }
            ),
            TypeKind::Generic(name) => write!(f, "'{}", name),
            TypeKind::Struct {
                name,
                ty_params,
                fields,
            } => write!(
                f,
                "{}{}{}",
                name,
                if let Some(ty_params) = ty_params {
                    ty_params.to_string()
                } else {
                    "".to_string()
                },
                if let Some(fields) = fields {
                    format!(
                        "{{ {} }}",
                        fields
                            .iter()
                            .map(|(n, t)| format!("{}: {}", n, t))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    "{}".to_string()
                }
            ),
            TypeKind::Fn {
                params,
                ret,
                ty_params,
            } => write!(
                f,
                "{}{}{}",
                if let Some(tp) = ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                },
                params,
                if let Some(t) = ret {
                    format!(" -> {}", t.to_string())
                } else {
                    "".to_string()
                }
            ),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Char => write!(f, "char"),
            TypeKind::String => write!(f, "string"),
            TypeKind::Pointer(t) => write!(f, "*{}", t),
            TypeKind::List(t) => write!(f, "{}[]", t),
            TypeKind::Array(t, s) => write!(f, "{}[{}]", t, s),
            TypeKind::Int(t) => write!(f, "{}", t),
            TypeKind::Float(t) => write!(f, "{}", t),
            TypeKind::Sequence(seq) => write!(
                f,
                "({})",
                seq.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeKind::Union(seq) => match seq.as_slice() {
                [t, Type {
                    kind: TypeKind::Nil,
                    ..
                }]
                | [Type {
                    kind: TypeKind::Nil,
                    ..
                }, t] => write!(f, "{}?", t),
                _ => write!(
                    f,
                    "{}",
                    seq.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" | ")
                ),
            },
            TypeKind::Nil => write!(f, "Nil"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeParams {
    pub tys: Vec<Type>,
    pub lb_span: Span,
    pub rb_span: Span,
}

impl From<Vec<Type>> for TypeParams {
    fn from(tys: Vec<Type>) -> TypeParams {
        TypeParams {
            tys,
            lb_span: Span::new(),
            rb_span: Span::new(),
        }
    }
}

impl fmt::Display for TypeParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.tys
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Clone, Debug, Eq, Hash)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Option<Span>,
}

impl Type {
    pub fn new(kind: TypeKind) -> Type {
        Type { kind, span: None }
    }

    pub fn from_expr(ex: &ast::Expr) -> Option<Vec<Type>> {
        match &ex.kind {
            ast::ExprKind::UnaryOp(ast::UnaryOp { expr, op, .. })
                if op == &ast::PrefixOp::Deref =>
            {
                if let Some(mut tys) = Type::from_expr(expr) {
                    Some(vec![Type::new(TypeKind::Pointer(Box::new(
                        tys.pop().unwrap(),
                    )))])
                } else {
                    None
                }
            }
            ast::ExprKind::Name(n) => {
                if let Some(t) = TypeKind::from_str(&n.name) {
                    Some(vec![Type::new(t)])
                } else {
                    None
                }
            }
            // ast::ExprKind::Index(idx) => {
            //     return Type::from_expr(&idx.lhs).map(|mut lhs| {
            //         if let Some(ty_params) = Type::from_expr(&idx.index) {
            //             lhs.apply_type_params(vec![ty_params]);
            //         }
            //         lhs
            //     })
            // }
            _ => None,
        }
    }

    pub fn id(&self) -> String {
        self.kind.to_string()
    }

    pub fn get_generics(&self) -> Vec<&Type> {
        let mut v = match &self.kind {
            TypeKind::Basic {
                ty_params, bounds, ..
            } => {
                let mut g = vec![];
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter());
                }

                if let Some(bounds) = bounds {
                    g.extend(bounds.get_generics());
                }

                g
            }
            TypeKind::Struct {
                ty_params, fields, ..
            } => {
                let mut g = vec![];
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter().flat_map(|t| t.get_generics()));
                }

                if let Some(fields) = fields {
                    g.extend(fields.iter().flat_map(|(_, t)| t.get_generics()));
                }
                g
            }
            TypeKind::Fn {
                params,
                ret,
                ty_params,
            } => {
                let mut g = params.get_generics();
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter().flat_map(|t| t.get_generics()));
                }
                if let Some(ret) = ret {
                    g.extend(ret.get_generics());
                }
                g
            }
            TypeKind::Pointer(t) | TypeKind::List(t) | TypeKind::Array(t, _) => t.get_generics(),
            TypeKind::Sequence(seq) | TypeKind::Union(seq) => {
                seq.iter().flat_map(|t| t.get_generics()).collect()
            }
            TypeKind::Unknown
            | TypeKind::Bool
            | TypeKind::Char
            | TypeKind::String
            | TypeKind::Nil
            | TypeKind::Generic(_)
            | TypeKind::TypeVar(_)
            | TypeKind::Int(..)
            | TypeKind::Float(..) => vec![],
        };

        v.dedup();
        v
    }

    pub fn get_generics_mut(&mut self) -> Vec<&mut Type> {
        if matches!(self.kind, TypeKind::Generic { .. }) {
            return vec![self];
        }

        let mut v = match &mut self.kind {
            TypeKind::Basic {
                ty_params, bounds, ..
            } => {
                let mut g = vec![];
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter_mut());
                }

                if let Some(bounds) = bounds {
                    g.extend(bounds.get_generics_mut());
                }

                g
            }
            TypeKind::Struct {
                ty_params, fields, ..
            } => {
                let mut g = vec![];
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter_mut().flat_map(|t| t.get_generics_mut()));
                }

                if let Some(fields) = fields {
                    g.extend(fields.iter_mut().flat_map(|(_, t)| t.get_generics_mut()));
                }
                g
            }
            TypeKind::Fn {
                params,
                ret,
                ty_params,
            } => {
                let mut g = params.get_generics_mut();
                if let Some(ty_params) = ty_params {
                    g.extend(ty_params.tys.iter_mut().flat_map(|t| t.get_generics_mut()));
                }
                if let Some(ret) = ret {
                    g.extend(ret.get_generics_mut());
                }
                g
            }
            TypeKind::Pointer(t) | TypeKind::List(t) | TypeKind::Array(t, _) => {
                t.get_generics_mut()
            }
            TypeKind::Sequence(seq) | TypeKind::Union(seq) => {
                seq.iter_mut().flat_map(|t| t.get_generics_mut()).collect()
            }
            TypeKind::Unknown
            | TypeKind::Bool
            | TypeKind::Char
            | TypeKind::String
            | TypeKind::Nil
            | TypeKind::TypeVar(_)
            | TypeKind::Int(..)
            | TypeKind::Float(..) => vec![],
            TypeKind::Generic { .. } => unreachable!(),
        };

        v.dedup();
        v
    }

    pub fn apply_type_params(&mut self, mut ty_params: Vec<Type>) {
        match &mut self.kind {
            TypeKind::List(t) => *t.as_mut() = ty_params.pop().unwrap(),
            _ => (),
        }
    }
}

impl PartialEq<Type> for Type {
    fn eq(&self, other: &Type) -> bool {
        self.kind == other.kind
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}
