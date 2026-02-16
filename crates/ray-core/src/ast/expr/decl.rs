use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use itertools::Itertools;
use ray_shared::{pathlib::Path, span::parsed::Parsed, ty::Ty, utils::join};
use ray_typing::types::{NominalKind, TyScheme};
use serde::{Deserialize, Serialize};

use crate::{
    ast::{Assign, Expr, Func, FuncSig, Modifier, Name, Node, TypeParams},
    strutils,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Extern {
    decl: Box<Node<Decl>>,
    src: Option<String>,
}

impl std::fmt::Display for Extern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.decl)
    }
}

impl Extern {
    pub fn new(decl: Node<Decl>) -> Self {
        Self {
            decl: Box::new(decl),
            src: None,
        }
    }

    pub fn decl_node(&self) -> &Node<Decl> {
        &self.decl
    }

    pub fn decl(&self) -> &Decl {
        &self.decl
    }

    pub fn decl_mut(&mut self) -> &mut Decl {
        self.decl.deref_mut()
    }

    pub fn src(&self) -> &Option<String> {
        &self.src
    }

    pub fn src_mut(&mut self) -> &mut Option<String> {
        &mut self.src
    }

    pub fn take(self) -> (Node<Decl>, Option<String>) {
        (*self.decl, self.src)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Decl {
    Mutable(Node<Name>, Vec<Modifier>),
    Name(Node<Name>, Vec<Modifier>),
    Declare(Assign),
    Func(Func),
    FnSig(FuncSig),
    Struct(Struct),
    Trait(Trait),
    TypeAlias(Node<Name>, Parsed<Ty>),
    Impl(Impl),
    /// Top-level execution context for a file.
    /// Contains all top-level statements (expressions) that are not declarations.
    /// Always has DefId with index 0 for the file.
    FileMain(Vec<Node<Expr>>),
    /// A test block: `test "name" { body }`.
    Test(TestDecl),
}

impl PartialOrd for Decl {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let i: usize = self.into();
        let j: usize = other.into();
        i.partial_cmp(&j)
    }
}

impl Ord for Decl {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let i: usize = self.into();
        let j: usize = other.into();
        i.cmp(&j)
    }
}

impl Into<usize> for &Decl {
    fn into(self) -> usize {
        match self {
            Decl::Trait(_) => 0,
            Decl::Struct(_) => 1,
            Decl::TypeAlias(_, _) => 2,
            Decl::Func(_) | Decl::FnSig(_) => 3,
            Decl::Impl(_) => 4,
            Decl::Declare(_) => 5,
            Decl::Mutable(_, _) | Decl::Name(_, _) => 6,
            Decl::FileMain(_) => 7,
            Decl::Test(_) => 8,
        }
    }
}

impl Decl {
    pub fn kind(&self) -> &'static str {
        match self {
            Decl::Mutable(_, _) => "Mutable",
            Decl::Name(_, _) => "Name",
            Decl::Declare(_) => "Declare",
            Decl::Func(_) => "Func",
            Decl::FnSig(_) => "FnSig",
            Decl::Struct(_) => "Struct",
            Decl::Trait(_) => "Trait",
            Decl::TypeAlias(_, _) => "TypeAlias",
            Decl::Impl(_) => "Impl",
            Decl::FileMain(_) => "FileMain",
            Decl::Test(_) => "Test",
        }
    }

    pub fn desc(&self) -> String {
        match self {
            Decl::Mutable(_, _) => todo!("mutable variable"),
            Decl::Name(_, _) => todo!("variable"),
            Decl::Declare(_) => todo!("variable"),
            Decl::Func(_) => str!("function"),
            Decl::FnSig(_) => str!("function signature"),
            Decl::Struct(_) => str!("struct"),
            Decl::Trait(_) => str!("trait"),
            Decl::TypeAlias(_, _) => str!("type alias"),
            Decl::Impl(_) => str!("impl"),
            Decl::FileMain(_) => str!("file main"),
            Decl::Test(_) => str!("test"),
        }
    }

    pub fn is_typed(&self) -> bool {
        match self {
            Decl::Struct(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) => true,
            Decl::Mutable(_, _) => todo!(),
            Decl::Name(_, _) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => f.sig.ty.is_some(),
            Decl::FnSig(sig) => sig.ty.is_some(),
            Decl::Impl(_) => false, // not entirely true, but we don't care here
            Decl::FileMain(_) => false, // FileMain is not explicitly typed
            Decl::Test(_) => false,
        }
    }

    pub fn get_ty(&self) -> Option<&TyScheme> {
        match self {
            Decl::Impl(_) | Decl::Struct(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) => todo!(),
            Decl::Mutable(_, _) => todo!(),
            Decl::Name(_, _) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => f.sig.ty.as_ref(),
            Decl::FnSig(sig) => sig.ty.as_ref(),
            Decl::FileMain(_) => None, // FileMain doesn't have an explicit type
            Decl::Test(_) => None,
        }
    }

    pub fn get_defs(&self) -> HashMap<&Path, Option<&TyScheme>> {
        let mut defs: HashMap<&Path, Option<&TyScheme>> = HashMap::new();
        match self {
            Decl::Mutable(_, _) => todo!(),
            Decl::Name(_, _) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => {
                defs.insert(&f.sig.path, f.sig.ty.as_ref());
            }
            Decl::FnSig(sig) => {
                defs.insert(&sig.path, sig.ty.as_ref());
            }
            Decl::Struct(_) => todo!(),
            Decl::Trait(tr) => {
                for func in tr.fields.iter() {
                    let func = variant!(func.deref(), if Decl::FnSig(func));
                    defs.insert(&func.path, func.ty.as_ref());
                }
            }
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(im) => {
                if let Some(externs) = &im.externs {
                    defs.extend(externs.iter().map(|d| d.get_defs()).concat());
                }

                if let Some(funcs) = &im.funcs {
                    defs.extend(funcs.iter().map(|d| d.get_defs()).concat());
                }

                if let Some(consts) = &im.consts {
                    defs.extend(
                        consts
                            .iter()
                            .flat_map(|d| d.lhs.path().map(|path| (path, None))),
                    );
                }
            }
            Decl::FileMain(_) => {
                // FileMain doesn't export named definitions
            }
            Decl::Test(_) => {
                // Test blocks don't export named definitions
            }
        }
        defs
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Struct {
    pub kind: NominalKind,
    pub path: Node<Path>,
    pub ty_params: Option<TypeParams>,
    pub fields: Option<Vec<Node<Name>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trait {
    pub path: Node<Path>,
    pub ty: Parsed<Ty>,
    pub fields: Vec<Node<Decl>>,
    pub super_trait: Option<Parsed<Ty>>,
    pub directives: Vec<Parsed<TraitDirective>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TraitDirectiveKind {
    Default,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraitDirective {
    pub kind: TraitDirectiveKind,
    pub args: Vec<Parsed<Ty>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Impl {
    pub ty: Parsed<Ty>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub externs: Option<Vec<Node<Decl>>>,
    /// Methods inside the impl block, wrapped as `Decl::Func`.
    pub funcs: Option<Vec<Node<Decl>>>,
    pub consts: Option<Vec<Node<Assign>>>,
    pub is_object: bool,
}

/// A test block declaration: `test "name" { body }`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TestDecl {
    /// The test name from the string literal.
    pub name: String,
    /// The block body of the test.
    pub body: Node<Expr>,
}

impl std::fmt::Display for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Mutable(n, mods) => write!(
                f,
                "({}mut {})",
                n,
                if !mods.is_empty() {
                    format!("{} ", join(mods, " "))
                } else {
                    String::new()
                }
            ),
            Decl::Name(n, mods) => write!(
                f,
                "({}declare {})",
                n,
                if !mods.is_empty() {
                    format!("{} ", join(mods, " "))
                } else {
                    String::new()
                }
            ),
            Decl::Declare(a) => write!(f, "(declare {})", a),
            Decl::TypeAlias(n, ty) => write!(f, "(type {} = {})", n, ty),
            Decl::Func(func) => write!(f, "{}", func),
            Decl::FnSig(sig) => write!(f, "(fn {})", sig),
            Decl::Struct(st) => {
                let tp = if let Some(tp) = &st.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                if let Some(fields) = &st.fields {
                    let fields = format!("{}\n", strutils::indent_lines_iter(fields, 2));
                    write!(f, "(struct {}{} {{\n{}}})", st.path, tp, fields)
                } else {
                    write!(f, "(struct {}{})", st.path, tp)
                }
            }
            Decl::Trait(tr) => {
                if tr.fields.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&tr.fields, 2));
                    write!(f, "(trait {}\n{})", tr.ty, methods)
                } else {
                    write!(f, "(trait {}\n)", tr.ty)
                }
            }
            Decl::Impl(im) => {
                let qualifiers = if im.qualifiers.len() != 0 {
                    format!("where {}", join(&im.qualifiers, " + "))
                } else {
                    str!("")
                };

                let funcs = if let Some(funcs) = &im.funcs {
                    let s = format!("{}", strutils::indent_lines_iter(funcs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let externs = if let Some(externs) = &im.externs {
                    let s = format!("{}", strutils::indent_lines_iter(externs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let consts = if let Some(consts) = &im.consts {
                    let s = format!("{}", strutils::indent_lines_iter(consts, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                if funcs.len() != 0 || externs.len() != 0 || consts.len() != 0 {
                    write!(
                        f,
                        "(impl {}{}\n{}{}{})",
                        im.ty, qualifiers, externs, consts, funcs
                    )
                } else {
                    write!(f, "(impl {}{})", im.ty, qualifiers)
                }
            }
            Decl::FileMain(stmts) => {
                if stmts.is_empty() {
                    write!(f, "(file-main)")
                } else {
                    let stmts_str = format!("{}\n", strutils::indent_lines_iter(stmts, 2));
                    write!(f, "(file-main\n{})", stmts_str)
                }
            }
            Decl::Test(test) => {
                write!(f, "(test \"{}\" {})", test.name, test.body)
            }
        }
    }
}

impl Decl {
    pub fn get_name(&self) -> Option<String> {
        match &self {
            Decl::Mutable(n, _) | Decl::Name(n, _) => Some(n.path.to_string()),
            Decl::Func(f) => f.sig.path.name(),
            Decl::FnSig(sig) => sig.path.name(),
            Decl::Struct(s) => s.path.name(),
            Decl::Trait(t) => Some(t.ty.name()),
            Decl::TypeAlias(_, _) | Decl::Impl(_) | Decl::Declare(_) | Decl::FileMain(_) => None,
            Decl::Test(test) => Some(test.name.clone()),
        }
    }
}
