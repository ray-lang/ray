use crate::{
    ast::{Decl, FnParam, FnSig, Name, Node, Path, SourceInfo, Struct, Type, TypeKind, TypeParams},
    pathlib::FilePath,
    span::{Source, Span},
};

use std::fmt;

#[derive(Debug)]
pub struct CType {
    pub name: String,
    pub ty_params: Option<Vec<Type>>,
    pub inputs: Option<Vec<(String, Type)>>,
    pub out_ty: Type,
    pub filepath: FilePath,
}

impl CType {
    pub fn convert_to_decl(self, span: Span) -> Node<Decl<SourceInfo>, SourceInfo> {
        if let Some(inputs) = self.inputs {
            Node::new(
                Decl::Extern(Box::new(Node::new(
                    Decl::Fn(FnSig {
                        path: Path::new(),
                        name: Some(self.name),
                        params: inputs
                            .into_iter()
                            .map(|(name, t)| {
                                if name.is_empty() {
                                    FnParam::Type(t)
                                } else {
                                    FnParam::Name(Name {
                                        name,
                                        ty: Some(t),
                                        span: Span::new(),
                                    })
                                }
                            })
                            .collect(),
                        ty_params: self
                            .ty_params
                            .map(|tys| {
                                Some(TypeParams {
                                    tys,
                                    lb_span: Span::new(),
                                    rb_span: Span::new(),
                                })
                            })
                            .unwrap_or_default(),
                        ret_ty: Some(self.out_ty),
                        span: Span::new(),
                        ty: None,
                        modifiers: vec![],
                        qualifiers: vec![],
                        doc_comment: None,
                        decorators: None,
                    }),
                    SourceInfo {
                        src: Source {
                            span: Some(span),
                            filepath: self.filepath.clone(),
                        },
                        path: Path::new(),
                        doc: None,
                    },
                ))),
                SourceInfo {
                    src: Source {
                        span: Some(span),
                        filepath: self.filepath,
                    },
                    path: Path::new(),
                    doc: None,
                },
            )
        } else {
            match self.out_ty.kind {
                TypeKind::Struct {
                    ty_params, fields, ..
                } => Node::new(
                    Decl::Struct(Struct {
                        name: Name {
                            name: self.name,
                            ty: None,
                            span: Span::new(),
                        },
                        fields: Some(
                            fields
                                .unwrap()
                                .into_iter()
                                .map(|(name, ty)| Name {
                                    name,
                                    ty: Some(ty),
                                    span: Span::new(),
                                })
                                .collect(),
                        ),
                        ty_params,
                    }),
                    SourceInfo {
                        src: Source {
                            span: Some(span),
                            filepath: self.filepath.clone(),
                        },
                        path: Path::new(),
                        doc: None,
                    },
                ),
                kind => Node::new(
                    Decl::TypeAlias(
                        Name {
                            name: self.name,
                            ty: None,
                            span: Span::new(),
                        },
                        Type { kind, span: None },
                    ),
                    SourceInfo {
                        src: Source {
                            span: Some(span),
                            filepath: self.filepath,
                        },
                        path: Path::new(),
                        doc: None,
                    },
                ),
            }
        }
    }
}

impl fmt::Display for CType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ty_params = if let Some(ref ty_params) = self.ty_params {
            format!(
                "[{}]",
                ty_params
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            "".to_string()
        };

        let inputs = if let Some(ref inputs) = self.inputs {
            format!(
                "({})",
                inputs
                    .iter()
                    .map(|(s, ty)| {
                        if s.len() == 0 {
                            format!("{}", ty)
                        } else {
                            format!("{}: {}", s, ty)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            "".to_string()
        };

        write!(f, "{}{}{} -> {}", self.name, ty_params, inputs, self.out_ty)
    }
}
