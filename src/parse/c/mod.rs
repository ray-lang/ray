use crate::errors::{RayError, RayErrorKind};
use crate::pathlib::FilePath;
use crate::span::{Pos, Span};
use crate::{ast, span::Source};

use lang_c::ast::{
    DeclarationSpecifier, Declarator, DeclaratorKind, DerivedDeclarator, ExternalDeclaration,
    SpecifierQualifier, StructDeclaration, StructKind, TranslationUnit, TypeSpecifier,
};
use lang_c::driver::{parse as cparse, Config};
use lang_c::span::Node;

use std::collections::HashSet;

macro_rules! c_ty_match {
    ($types:ident {
        $(
            $( ($( $pattern: pat ),+) )|+ => $r:expr
        ),+
    }) => {
        match () {
            $(
                _ if $(c_ty_occurs!($types, $($pattern),+))||+ => Some($r)
            ),+,
            _ => None
        }
    }
}

macro_rules! c_ty_occurs {
    ($s:ident, $($p: pat),+) => {{
        let mut set = HashSet::new();
        $s.len() == count_pat!($($p),+) && $s.iter()
            .fold(0, |c, u| {
                let mut skip = vec![];
                let idx = loop {
                    let idx = index_match!(u, skip, $($p,)+);
                    if idx == -1 {
                        break idx;
                    }

                    if !set.contains(&idx) {
                        set.insert(idx);
                        break idx;
                    }

                    skip.push(idx);
                };

                if idx != -1 { c + 1 } else { c }
            }) == $s.len()
    }};
}

macro_rules! index_match {
    (@step $_x:expr, $_skip_idx:expr, $_idx:expr,) => (-1);
    (@step $x:expr, $skip:ident, $idx:expr, $head:pat, $($tail:pat,)*) => {
        (if !$skip.contains(&$idx) && matches!($x, $head) {
            $idx
        } else {
            index_match!(@step $x, $skip, $idx + 1, $($tail,)*)
        })
    };
    ($x:expr, $skip:ident, $($p: pat,)*) => {
        index_match!(@step $x, $skip, 0, $($p,)*)
    };
}

macro_rules! count_pat {
    () => (0);
    ($head: pat) => (1);
    ($head: pat, $($tail: pat),*) => (1 + count_pat!($($tail),*))
}

impl From<lang_c::driver::Error> for RayError {
    fn from(err: lang_c::driver::Error) -> RayError {
        use lang_c::driver::Error::*;
        match err {
            PreprocessorError(io_err) => RayError::from(io_err),
            SyntaxError(syn) => RayError {
                kind: RayErrorKind::Parse,
                src: vec![Source {
                    filepath: FilePath::new(),
                    span: Some(Span::from(Pos {
                        lineno: syn.line,
                        col: syn.column,
                        offset: syn.offset,
                    })),
                }],
                msg: "unexpected token".to_string(),
            },
        }
    }
}

fn get_id(dec: &Declarator) -> String {
    match dec.kind.node {
        DeclaratorKind::Identifier(ref id) => id.node.name.clone(),
        _ => "".to_string(),
    }
}

fn make_ptr_ty(kind: ast::TypeKind, ptr: usize, ty_params: &mut Vec<ast::Type>) -> ast::Type {
    let mut ty = ast::Type { kind, span: None };
    for _ in 0..ptr {
        match ty.kind {
            ast::TypeKind::Sequence(items) if items.len() == 0 => {
                // void*
                let idx = ty_params.len();
                ty = ast::Type {
                    kind: ast::TypeKind::basic(&format!("T{}", idx)),
                    span: None,
                };
                ty_params.push(ty.clone());
            }
            _ => (),
        }

        ty = ast::Type {
            kind: ast::TypeKind::pointer(ty),
            span: None,
        };
    }
    ty
}

fn get_type(
    specs: &Vec<Node<DeclarationSpecifier>>,
    ptr: usize,
    ty_params: &mut Vec<ast::Type>,
) -> ast::Type {
    let kind = make_type(
        specs
            .iter()
            .flat_map(|s| match s.node {
                DeclarationSpecifier::TypeSpecifier(ref t) => Some(&t.node),
                _ => None,
            })
            .collect(),
    );

    make_ptr_ty(kind, ptr, ty_params)
}

fn get_pointers(decl: &Declarator) -> usize {
    decl.derived
        .iter()
        .filter(|d| matches!(d.node, DerivedDeclarator::Pointer(_)))
        .count()
}

fn get_inputs(
    decl: &Declarator,
    ty_params: &mut Vec<ast::Type>,
) -> Option<Vec<(String, ast::Type)>> {
    decl.derived.iter().find_map(|d| match d.node {
        DerivedDeclarator::Function(ref fn_dec) => {
            let inputs = fn_dec
                .node
                .parameters
                .iter()
                .enumerate()
                .map(|(idx, p)| {
                    // get the name and number of pointers
                    let (ptr, id) = p.node.declarator.as_ref().map_or_else(
                        || (0, format!("arg{}", idx)),
                        |d| {
                            let ptr = get_pointers(&d.node);
                            let id = get_id(&d.node);
                            (
                                ptr,
                                if id.len() == 0 {
                                    format!("arg{}", idx)
                                } else {
                                    id
                                },
                            )
                        },
                    );

                    // get the type
                    let ty = get_type(&p.node.specifiers, ptr, ty_params);
                    (id, ty)
                })
                .collect::<Vec<_>>();
            if inputs.len() == 1 && inputs.first().map(|(_, ty)| ty.kind.is_unit()).unwrap() {
                // handle the (void) case
                Some(vec![])
            } else {
                Some(inputs)
            }
        }
        _ => None,
    })
}

fn get_struct_fields(
    struct_decls: &Vec<Node<StructDeclaration>>,
    ty_params: &mut Vec<ast::Type>,
) -> Vec<(String, ast::Type)> {
    struct_decls
        .iter()
        .flat_map(|decl| match decl.node {
            StructDeclaration::Field(ref field) => {
                let kind = make_type(
                    field
                        .node
                        .specifiers
                        .iter()
                        .flat_map(|s| match s.node {
                            SpecifierQualifier::TypeSpecifier(ref ty_spec) => Some(&ty_spec.node),
                            _ => None,
                        })
                        .collect(),
                );
                field
                    .node
                    .declarators
                    .iter()
                    .map(|struct_decl| {
                        let decl = struct_decl.node.declarator.as_ref().unwrap();
                        let id = get_id(&decl.node);
                        let ptr = get_pointers(&decl.node);
                        let ty = make_ptr_ty(kind.clone(), ptr, ty_params);
                        (id, ty)
                    })
                    .collect::<Vec<_>>()
            }
            _ => vec![],
        })
        .collect::<Vec<_>>()
}

fn make_type(ty_specs: Vec<&TypeSpecifier>) -> ast::TypeKind {
    use TypeSpecifier::*;
    let kind = c_ty_match!(ty_specs {
        /* unsigned char */
        (Unsigned, Char) => ast::TypeKind::Int(ast::IntTy::UInt8),
        /* char | signed char */
        (Signed, Char) | (Char) => ast::TypeKind::Int(ast::IntTy::Int8),
        /* unsigned | unsigned short | unsigned int | unsigned short int */
        (Unsigned) | (Unsigned, Short) | (Unsigned, Int) | (Unsigned, Short, Int) => {
            ast::TypeKind::Int(ast::IntTy::UInt16)
        },
        /* short | int | short int | signed int | signed short | signed short int */
        (Short) | (Int) | (Short, Int) | (Signed, Int) | (Signed, Short) | (Signed, Short, Int) => {
            ast::TypeKind::Int(ast::IntTy::Int16)
        },
        /* unsigned long | unsigned long int */
        (Unsigned, Long) | (Unsigned, Long, Int) => ast::TypeKind::Int(ast::IntTy::UInt32),
        /* long | long int | signed long | signed long int */
        (Long) | (Long, Int) | (Signed, Long) | (Signed, Long, Int) => ast::TypeKind::Int(ast::IntTy::Int32),
        /* long long | long long int | signed long long | signed long long int */
        (Long, Long) | (Long, Long, Int) | (Signed, Long, Long) | (Signed, Long, Long, Int) => ast::TypeKind::Int(ast::IntTy::Int64),
        /* usigned long long | usigned long long int */
        (Unsigned, Long, Long) | (Unsigned, Long, Long, Int) => ast::TypeKind::Int(ast::IntTy::UInt64),
        /* float */
        (Float) => ast::TypeKind::Float(ast::FloatTy::Float32),
        /* double */
        (Double) => ast::TypeKind::Float(ast::FloatTy::Float32),
        /* long double */
        (Long, Double) => ast::TypeKind::Float(ast::FloatTy::Float128),
        /* void */
        (Void) => ast::TypeKind::unit()
    });

    if let Some(kind) = kind {
        kind
    } else {
        let k = ty_specs.iter().find_map(|t| match t {
            TypeSpecifier::TypedefName(id) => Some(ast::TypeKind::Basic {
                name: id.node.name.clone(),
                ty_params: None,
                bounds: None,
            }),
            TypeSpecifier::Struct(ref struct_ty) => match struct_ty.node.kind.node {
                StructKind::Struct => {
                    let name = struct_ty
                        .node
                        .identifier
                        .as_ref()
                        .map_or_else(|| "".to_string(), |id| id.node.name.clone());
                    let mut ty_params = vec![];
                    let fields = struct_ty
                        .node
                        .declarations
                        .as_ref()
                        .map(|struct_decls| get_struct_fields(struct_decls, &mut ty_params));
                    Some(ast::TypeKind::Struct {
                        name,
                        ty_params: if ty_params.len() != 0 {
                            Some(ast::TypeParams::from(ty_params))
                        } else {
                            None
                        },
                        fields,
                    })
                }
                StructKind::Union => None,
            },
            _ => None,
        });

        if let Some(k) = k {
            k
        } else {
            unimplemented!("make_type from C type spec: {:?}", ty_specs)
        }
    }
}

fn offset_to_pos(input: &str, offset: usize) -> Pos {
    let before = &input[..offset];
    let lineno = before.as_bytes().iter().filter(|&&c| c == b'\n').count() + 1;
    let col = before.chars().rev().take_while(|&c| c != '\n').count() + 1;
    Pos {
        lineno,
        col,
        offset,
    }
}

pub fn parse(
    fpath: &FilePath,
    include_paths: &Vec<FilePath>,
) -> Result<Vec<(ast::CType, Span)>, lang_c::driver::Error> {
    let mut config = Config::default();
    for p in include_paths {
        config.cpp_options.push(format!("-I{}", p));
    }
    let p = cparse(&config, &fpath)?;
    let TranslationUnit(nodes) = p.unit;
    let mut types = vec![];
    for n in nodes.iter() {
        let start = offset_to_pos(&p.source, n.span.start);
        let end = offset_to_pos(&p.source, n.span.end);
        let ty = match n.node {
            ExternalDeclaration::Declaration(ref declaration) => {
                let mut ty_params = vec![];
                let (decl_name, inputs, out_ty_ptrs) = match declaration.node.declarators.first() {
                    Some(init_dec) => {
                        let decl = &init_dec.node.declarator.node;
                        let name = get_id(decl);
                        let inputs = get_inputs(decl, &mut ty_params);
                        let out_ty_ptrs = get_pointers(decl);
                        (name, inputs, out_ty_ptrs)
                    }
                    _ => continue,
                };

                if declaration.node.specifiers.len() == 0 {
                    continue;
                }

                let out_ty = match decl_name.as_str() {
                    s if s == "uintptr_t" || s == "intptr_t" => {
                        let int_ty = if s == "intptr_t" {
                            ast::IntTy::Int
                        } else {
                            ast::IntTy::UInt
                        };
                        let kind = ast::TypeKind::Int(int_ty);
                        make_ptr_ty(kind, out_ty_ptrs, &mut ty_params)
                    }
                    _ => get_type(&declaration.node.specifiers, out_ty_ptrs, &mut ty_params),
                };
                ast::CType {
                    name: decl_name,
                    ty_params: if ty_params.len() != 0 {
                        Some(ty_params)
                    } else {
                        None
                    },
                    filepath: fpath.clone(),
                    inputs,
                    out_ty,
                }
            }
            ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                let mut ty_params = vec![];
                let name = get_id(&fn_def.node.declarator.node);
                let inputs = get_inputs(&fn_def.node.declarator.node, &mut ty_params);
                let out_ty_ptrs = get_pointers(&fn_def.node.declarator.node);
                let out_ty = get_type(&fn_def.node.specifiers, out_ty_ptrs, &mut ty_params);
                ast::CType {
                    name,
                    ty_params: if ty_params.len() != 0 {
                        Some(ty_params)
                    } else {
                        None
                    },
                    filepath: fpath.clone(),
                    out_ty,
                    inputs,
                }
            }
            _ => continue,
        };

        types.push((ty, Span { start, end }));
    }

    Ok(types)
}
