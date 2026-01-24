//! Type path for instantiated types used in monomorphization and codegen.
//!
//! TypePath represents a type with its type arguments fully resolved,
//! suitable for symbol generation and monomorphization. Unlike ItemPath
//! (which is just a definition identity), TypePath carries the full
//! instantiated type information.

use serde::{Deserialize, Serialize};

use crate::ty::Ty;

use super::ItemPath;

/// A type path represents an instantiated type for codegen and monomorphization.
///
/// This is used when we need to generate symbols for specific type instantiations,
/// such as `List[Int]` vs `List[String]`.
///
/// Note: This is separate from function mangling, which uses `Path` with `FuncType`
/// suffix for signature-based disambiguation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypePath {
    /// Nominal type with optional type args: `List[Int]`, `Dict[String, Int]`
    Nominal { base: ItemPath, args: Vec<Ty> },
    /// Array with element type and size: `[u8; 32]`
    Array { elem: Ty, size: usize },
    /// Tuple: `(Int, String)`
    Tuple(Vec<Ty>),
}

impl std::fmt::Display for TypePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypePath::Nominal { base, args } => {
                if args.is_empty() {
                    write!(f, "{}", base)
                } else {
                    let args_str = args
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "{}[{}]", base, args_str)
                }
            }
            TypePath::Array { elem, size } => {
                write!(f, "[{}; {}]", elem, size)
            }
            TypePath::Tuple(elems) => {
                let elems_str = elems
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", elems_str)
            }
        }
    }
}

impl TypePath {
    /// Create a nominal type path with no type arguments.
    pub fn simple(base: ItemPath) -> Self {
        TypePath::Nominal {
            base,
            args: Vec::new(),
        }
    }

    /// Create a nominal type path with type arguments.
    pub fn with_args(base: ItemPath, args: Vec<Ty>) -> Self {
        TypePath::Nominal { base, args }
    }

    /// Create an array type path.
    pub fn array(elem: Ty, size: usize) -> Self {
        TypePath::Array { elem, size }
    }

    /// Create a tuple type path.
    pub fn tuple(elems: Vec<Ty>) -> Self {
        TypePath::Tuple(elems)
    }

    /// Get the definition identity for lookups (Nominal only).
    ///
    /// Returns `Some(&ItemPath)` for nominal types, `None` for arrays and tuples.
    pub fn item_path(&self) -> Option<&ItemPath> {
        match self {
            TypePath::Nominal { base, .. } => Some(base),
            TypePath::Array { .. } | TypePath::Tuple(_) => None,
        }
    }

    /// Generate a mangled symbol name for this type path.
    ///
    /// This produces a string suitable for use as a symbol name in codegen.
    pub fn to_mangled(&self) -> String {
        match self {
            TypePath::Nominal { base, args } => {
                if args.is_empty() {
                    base.to_string()
                } else {
                    let args_str = args
                        .iter()
                        .map(|t| mangle_ty(t))
                        .collect::<Vec<_>>()
                        .join(",");
                    format!("{}[{}]", base, args_str)
                }
            }
            TypePath::Array { elem, size } => {
                format!("[{};{}]", mangle_ty(elem), size)
            }
            TypePath::Tuple(elems) => {
                let elems_str = elems
                    .iter()
                    .map(|t| mangle_ty(t))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("({})", elems_str)
            }
        }
    }
}

/// Mangle a type into a string suitable for symbol names.
fn mangle_ty(ty: &Ty) -> String {
    match ty {
        Ty::Const(path) => path.to_string(),
        Ty::Proj(path, args) => {
            if args.is_empty() {
                path.to_string()
            } else {
                let args_str = args.iter().map(|t| mangle_ty(t)).collect::<Vec<_>>().join(",");
                format!("{}[{}]", path, args_str)
            }
        }
        Ty::Var(v) => v.0.to_string(),
        Ty::Func(params, ret) => {
            let params_str = params
                .iter()
                .map(|t| mangle_ty(t))
                .collect::<Vec<_>>()
                .join(",");
            format!("<({}):{}>", params_str, mangle_ty(ret))
        }
        Ty::Ref(inner) => format!("*{}", mangle_ty(inner)),
        Ty::RawPtr(inner) => format!("rawptr[{}]", mangle_ty(inner)),
        Ty::Tuple(elems) => {
            let elems_str = elems
                .iter()
                .map(|t| mangle_ty(t))
                .collect::<Vec<_>>()
                .join(",");
            format!("({})", elems_str)
        }
        Ty::Array(elem, size) => format!("[{};{}]", mangle_ty(elem), size),
        Ty::Any => "any".to_string(),
        Ty::Never => "never".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use crate::pathlib::{ItemPath, Path, TypePath};
    use crate::ty::Ty;

    #[test]
    fn type_path_nominal_simple() {
        let item_path = ItemPath::new(Path::from("core::list"), vec!["List".into()]);
        let type_path = TypePath::simple(item_path.clone());

        assert_eq!(type_path.to_string(), "core::list::List");
        assert_eq!(type_path.item_path(), Some(&item_path));
    }

    #[test]
    fn type_path_nominal_with_args() {
        let item_path = ItemPath::new(Path::from("core::list"), vec!["List".into()]);
        let type_path = TypePath::with_args(item_path.clone(), vec![Ty::int()]);

        assert_eq!(type_path.to_string(), "core::list::List[int]");
        assert_eq!(type_path.item_path(), Some(&item_path));
    }

    #[test]
    fn type_path_array() {
        let type_path = TypePath::array(Ty::u8(), 32);

        assert_eq!(type_path.to_string(), "[u8; 32]");
        assert_eq!(type_path.item_path(), None);
    }

    #[test]
    fn type_path_tuple() {
        let type_path = TypePath::tuple(vec![Ty::int(), Ty::string()]);

        assert_eq!(type_path.to_string(), "(int, string)");
        assert_eq!(type_path.item_path(), None);
    }

    #[test]
    fn type_path_to_mangled() {
        let item_path = ItemPath::new(Path::from("core::list"), vec!["List".into()]);
        let type_path = TypePath::with_args(item_path, vec![Ty::int()]);

        assert_eq!(type_path.to_mangled(), "core::list::List[int]");
    }

    #[test]
    fn type_path_mangled_nested() {
        let outer = ItemPath::new(Path::from("core::dict"), vec!["Dict".into()]);
        let type_path = TypePath::with_args(outer, vec![Ty::string(), Ty::int()]);

        assert_eq!(type_path.to_mangled(), "core::dict::Dict[string,int]");
    }
}
