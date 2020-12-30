use crate::{ast, pathlib::FilePath, span::Span};

use std::fmt;

#[derive(Debug)]
pub struct CType {
    pub name: String,
    pub ty_params: Option<Vec<ast::Type>>,
    pub inputs: Option<Vec<(String, ast::Type)>>,
    pub out_ty: ast::Type,
    pub filepath: FilePath,
}

impl CType {
    pub fn convert_to_decl(self, span: Span, module_id: u64, next_ast_id: &mut u64) -> ast::Decl {
        let first_id = *next_ast_id;
        *next_ast_id += 1;
        if let Some(inputs) = self.inputs {
            let second_id = *next_ast_id;
            *next_ast_id += 1;
            ast::Decl {
                id: ast::Id {
                    module_id,
                    local_id: first_id,
                },
                kind: ast::DeclKind::Extern(Box::new(ast::Decl {
                    id: ast::Id {
                        module_id,
                        local_id: second_id,
                    },
                    kind: ast::DeclKind::Fn(ast::FnSig {
                        name: Some(self.name),
                        params: inputs
                            .into_iter()
                            .map(|(name, t)| ast::Name {
                                name,
                                ty: Some(t),
                                span: Span::new(),
                                default: None,
                            })
                            .collect(),
                        ty_params: self
                            .ty_params
                            .map(|tys| {
                                Some(ast::TypeParams {
                                    tys,
                                    lb_span: Span::new(),
                                    rb_span: Span::new(),
                                })
                            })
                            .unwrap_or_default(),
                        ret_ty: Some(self.out_ty),
                        ty: None,
                        modifiers: vec![],
                        doc_comment: None,
                        decorators: None,
                    }),
                    span,
                    filepath: self.filepath.clone(),
                })),
                span,
                filepath: self.filepath,
            }
        } else {
            match self.out_ty.kind {
                ast::TypeKind::Struct {
                    ty_params, fields, ..
                } => ast::Decl {
                    id: ast::Id {
                        module_id,
                        local_id: first_id,
                    },
                    kind: ast::DeclKind::Struct(ast::Struct {
                        name: ast::Name {
                            name: self.name,
                            ty: None,
                            span: Span::new(),
                            default: None,
                        },
                        fields: Some(
                            fields
                                .unwrap()
                                .into_iter()
                                .map(|(name, ty)| ast::Name {
                                    name,
                                    ty: Some(ty),
                                    span: Span::new(),
                                    default: None,
                                })
                                .collect(),
                        ),
                        ty_params,
                    }),
                    filepath: self.filepath.clone(),
                    span,
                },
                kind => ast::Decl {
                    id: ast::Id {
                        module_id,
                        local_id: first_id,
                    },
                    kind: ast::DeclKind::TypeAlias(
                        ast::Name {
                            name: self.name,
                            ty: None,
                            span: Span::new(),
                            default: None,
                        },
                        ast::Type { kind, span: None },
                    ),
                    filepath: self.filepath,
                    span,
                },
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
