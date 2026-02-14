use std::fmt::Display;

use ray_core::ast::Modifier;
use ray_frontend::queries::libraries::LibraryData;
use ray_lir as lir;
use ray_shared::{
    node_id::NodeId,
    pathlib::{FilePath, Path},
    span::Span,
    ty::Ty,
};
use serde::{Deserialize, Serialize};

/// Binary serialization format for compiled libraries.
///
/// A RayLib file contains:
/// - `data`: The library metadata (type schemes, struct/trait/impl definitions,
///   operators, source map) used during compilation of dependent code
/// - `program`: The LIR representation for codegen
#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub data: LibraryData,
    pub program: lir::Program,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefinitionKind {
    Function {
        params: Vec<(Path, Option<Ty>)>,
        return_ty: Option<Ty>,
        type_params: Option<Vec<Ty>>,
        modifiers: Vec<Modifier>,
        qualifiers: Vec<Ty>,
        parent: Option<Box<DefinitionKind>>,
    },
    Trait {
        ty: Ty,
    },
    Impl {
        ty: Ty,
        qualifiers: Vec<Ty>,
    },
    Struct {
        path: Path,
        type_params: Option<Vec<Ty>>,
    },
    Name {
        ty: Option<Ty>,
        parent: Option<Box<DefinitionKind>>,
    },
    Variable {
        ty: Option<Ty>,
    },
    TypeAlias,
    Unknown,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinitionRecord {
    pub id: NodeId,
    pub display_path: Path,
    pub file: Option<FilePath>,
    pub span: Option<Span>,
    pub doc: Option<String>,
    pub kind: DefinitionKind,
}

impl Display for DefinitionRecord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_kind(
            f: &mut std::fmt::Formatter<'_>,
            kind: &DefinitionKind,
            display_path: Option<&Path>,
        ) -> std::fmt::Result {
            let path = display_path.map(|p| p.name().unwrap_or_else(|| p.to_string()));

            match kind {
                DefinitionKind::Function {
                    params,
                    return_ty,
                    type_params,
                    modifiers,
                    qualifiers,
                    parent,
                } => {
                    if let Some(parent) = parent {
                        write_kind(f, parent, None)?;
                    }

                    let path = path.unwrap_or_else(|| "".to_string());

                    let modifiers_str = if !modifiers.is_empty() {
                        let mods = modifiers
                            .iter()
                            .map(|m| m.to_string())
                            .collect::<Vec<_>>()
                            .join(" ");
                        format!("{} ", mods)
                    } else {
                        String::new()
                    };

                    let params_str = params
                        .iter()
                        .map(|(path, ty)| {
                            if let Some(ty) = ty {
                                format!("{}: {}", path.to_short_name(), ty)
                            } else {
                                format!("{}", path.to_short_name())
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(", ");

                    let type_params_str = if let Some(type_params) = type_params {
                        let tys = type_params
                            .iter()
                            .map(|ty| ty.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("[{}]", tys)
                    } else {
                        String::new()
                    };

                    let return_ty_str = if let Some(return_ty) = return_ty {
                        format!(" -> {}", return_ty)
                    } else {
                        String::new()
                    };

                    let qualifiers_str = if !qualifiers.is_empty() {
                        let quals = qualifiers
                            .iter()
                            .map(|q| q.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(" where {}", quals)
                    } else {
                        String::new()
                    };

                    writeln!(
                        f,
                        "{}fn {}{}({}){}{}",
                        modifiers_str,
                        path,
                        type_params_str,
                        params_str,
                        return_ty_str,
                        qualifiers_str
                    )
                }
                DefinitionKind::Trait { ty } => {
                    writeln!(f, "trait {}", ty)
                }
                DefinitionKind::Impl { ty, qualifiers } => {
                    let qualifiers_str = if !qualifiers.is_empty() {
                        let quals = qualifiers
                            .iter()
                            .map(|q| q.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(" where {}", quals)
                    } else {
                        String::new()
                    };
                    writeln!(f, "impl {}{}", ty, qualifiers_str)
                }
                DefinitionKind::Struct { path, type_params } => {
                    let type_params_str = if let Some(type_params) = type_params {
                        let tys = type_params
                            .iter()
                            .map(|ty| ty.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("[{}]", tys)
                    } else {
                        String::new()
                    };
                    writeln!(f, "struct {}{}", path, type_params_str)
                }
                DefinitionKind::Name { ty, parent } => {
                    if let Some(parent) = parent {
                        write_kind(f, parent, None)?;
                    }

                    if let Some(ty) = ty {
                        writeln!(f, "{}: {}", path.unwrap(), ty)
                    } else {
                        writeln!(f, "{}", path.unwrap())
                    }
                }
                DefinitionKind::Variable { ty } => {
                    if let Some(ty) = ty {
                        writeln!(f, "{}: {}", path.unwrap(), ty)
                    } else {
                        writeln!(f, "{}", path.unwrap())
                    }
                }
                DefinitionKind::Unknown => writeln!(f, "{}", path.unwrap()),
                DefinitionKind::TypeAlias => Ok(()),
            }
        }

        writeln!(f, "```ray")?;

        write_kind(f, &self.kind, Some(&self.display_path))?;

        writeln!(f, "```")?;

        if let Some(doc) = &self.doc {
            if !doc.trim().is_empty() {
                write!(f, "\n\n")?;
                write!(f, "{}", doc.trim())?;
            }
        }

        Ok(())
    }
}

/// Serialize a library to binary format for distribution.
pub fn serialize(data: LibraryData, program: lir::Program) -> Vec<u8> {
    bincode::serialize(&RayLib { data, program }).unwrap()
}
