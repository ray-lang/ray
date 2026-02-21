//! Auto-derivable trait impl queries.
//!
//! Provides the `auto_derive_impls` query which produces synthetic trait impls
//! for structs that don't have explicit implementations. Uses `parse_file_raw`
//! (not `parse_file`) to break the circular dependency between parsing and impl
//! lookup.

use std::{collections::HashSet, sync::Arc};

use ray_core::{
    ast::{
        Curly, CurlyElement, Decl, Dot, Expr, FnParam, Func, FuncSig, Impl, Name, Node, Struct,
        token::{Token, TokenKind},
    },
    sourcemap::SourceMap,
};
use ray_query_macros::query;
use ray_shared::{
    def::{DefHeader, DefId, DefKind},
    file_id::FileId,
    node_id::NodeId,
    pathlib::{FilePath, ItemPath, Path},
    resolution::DefTarget,
    span::{Source, Span, parsed::Parsed},
    ty::Ty,
};
use ray_typing::types::TyScheme;
use serde::{Deserialize, Serialize};

use crate::{
    queries::{
        defs::explicit_impls_for_trait,
        parse::{ParseResult, parse_file_raw},
        resolve::resolve_builtin,
    },
    query::{Database, Query},
};

/// Auto-derivable traits. Currently only Clone; designed for future expansion.
pub(crate) const AUTO_DERIVE_TRAITS: &[&str] = &["Clone"];

/// Synthetic impls produced by auto-derivation for a single file.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesizedImpls {
    pub decls: Vec<Node<Decl>>,
    pub defs: Vec<DefHeader>,
    pub source_map: SourceMap,
    pub synthetic_defs: HashSet<DefId>,
}

/// A (struct, trait) pair that needs a synthetic impl.
struct AutoDeriveEntry {
    struct_def_id: DefId,
    trait_name: String,
}

/// Produces synthetic trait impls for structs that lack explicit implementations.
///
/// Returns only the synthetic parts (decls, defs, source map, synthetic def IDs).
/// The caller (`parse_file`) merges these into the raw parse result.
///
/// All dependencies use `parse_file_raw`, not `parse_file`, so this query can
/// safely be called from `parse_file` without creating a cycle.
#[query]
pub fn auto_derive_impls(db: &Database, file_id: FileId) -> Arc<SynthesizedImpls> {
    let raw = parse_file_raw(db, file_id);
    let candidates = auto_derive_impl_candidates(db, file_id, &raw);

    let mut decls = Vec::new();
    let mut defs = Vec::new();
    let mut source_map = SourceMap::default();
    let mut synthetic_defs = HashSet::new();

    if !candidates.is_empty() {
        let mut next_index = raw.defs.iter().map(|h| h.def_id.index).max().unwrap_or(0) + 1;
        let filepath = raw.ast.filepath.clone();

        for entry in &candidates {
            let Some(struct_header) = raw.defs.iter().find(|h| h.def_id == entry.struct_def_id)
            else {
                continue;
            };
            let Some(struct_ast) = raw
                .ast
                .decls
                .iter()
                .find(|d| d.id == struct_header.root_node)
                .and_then(|d| match &d.value {
                    Decl::Struct(s) => Some(s),
                    _ => None,
                })
            else {
                continue;
            };

            synthesize_trait_impl(
                &entry.trait_name,
                file_id,
                &mut next_index,
                struct_header,
                struct_ast,
                &filepath,
                &mut decls,
                &mut defs,
                &mut source_map,
                &mut synthetic_defs,
            );
        }
    }

    Arc::new(SynthesizedImpls {
        decls,
        defs,
        source_map,
        synthetic_defs,
    })
}

/// Determines which (struct, trait) pairs in a file need synthetic impls.
///
/// For each auto-derivable trait, checks whether:
/// 1. The trait is in scope for the file (via `resolve_builtin`)
/// 2. The struct does not already have an explicit impl (via `explicit_impls_for_trait`)
fn auto_derive_impl_candidates(
    db: &Database,
    file_id: FileId,
    raw: &ParseResult,
) -> Vec<AutoDeriveEntry> {
    let mut entries = Vec::new();

    for trait_name in AUTO_DERIVE_TRAITS {
        let Some(trait_target) = resolve_builtin(db, file_id, trait_name.to_string()) else {
            continue;
        };

        let explicit_impls = explicit_impls_for_trait(db, trait_target);

        for struct_header in raw
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Struct))
        {
            let struct_target = DefTarget::Workspace(struct_header.def_id);
            let has_explicit = explicit_impls
                .iter()
                .any(|e| e.implementing_type_target.as_ref() == Some(&struct_target));

            if !has_explicit {
                entries.push(AutoDeriveEntry {
                    struct_def_id: struct_header.def_id,
                    trait_name: trait_name.to_string(),
                });
            }
        }
    }

    entries
}

// ---------------------------------------------------------------------------
// Synthetic impl generation
// ---------------------------------------------------------------------------

/// Creates one synthetic `NodeId` per flattened type reference in `ty`.
/// Each ID is registered in the source map and marked synthetic.
/// Must be called within an active `NodeId::enter_def` scope.
fn make_synthetic_ids(ty: &Ty, source_map: &mut SourceMap, src: &Source) -> Vec<NodeId> {
    ty.flatten()
        .into_iter()
        .map(|_| {
            let id = NodeId::new();
            source_map.set_src_id(id, src.clone());
            source_map.mark_synthetic(id);
            id
        })
        .collect()
}

/// Generates a synthetic `impl Trait[S] { ... }` for a single struct + trait combination.
///
/// The trait-specific method(s) are built by dispatching to a per-trait body builder.
/// The outer impl wrapping, DefId allocation, and DefHeader registration are generic.
fn synthesize_trait_impl(
    trait_name: &str,
    file_id: FileId,
    next_index: &mut u32,
    struct_header: &DefHeader,
    struct_ast: &Struct,
    filepath: &FilePath,
    decls: &mut Vec<Node<Decl>>,
    defs: &mut Vec<DefHeader>,
    source_map: &mut SourceMap,
    synthetic_defs: &mut HashSet<DefId>,
) {
    let impl_def_id = DefId::new(file_id, *next_index);
    *next_index += 1;
    let method_def_id = DefId::new(file_id, *next_index);
    *next_index += 1;

    let src = Source {
        filepath: filepath.clone(),
        span: None,
        ..Default::default()
    };

    // Build the struct's type (with type params if generic)
    let struct_item_path = ItemPath::from(struct_header.name.as_str());

    let ty_param_tys: Vec<Ty> = struct_ast
        .ty_params
        .as_ref()
        .map(|tp| tp.tys.iter().map(|p| p.value().clone()).collect())
        .unwrap_or_default();

    let struct_ty = if ty_param_tys.is_empty() {
        Ty::Const(struct_item_path)
    } else {
        Ty::Proj(struct_item_path, ty_param_tys)
    };

    // Trait[StructTy]
    let impl_ty = Ty::Proj(ItemPath::from(trait_name), vec![struct_ty.clone()]);

    // Dispatch to per-trait method builder
    let (method_name, method_decl, method_root_node) = match trait_name {
        "Clone" => build_clone_method(method_def_id, struct_ast, &struct_ty, &src, source_map),
        _ => unreachable!("unsupported auto-derive trait: {trait_name}"),
    };

    // Build impl decl within the impl's NodeId scope
    let impl_decl;
    let impl_root_node;
    {
        let _impl_guard = NodeId::enter_def(impl_def_id);

        let impl_ty_ids = make_synthetic_ids(&impl_ty, source_map, &src);
        let mut parsed_impl_ty = Parsed::new(impl_ty, src.clone());
        parsed_impl_ty.set_synthetic_ids(impl_ty_ids);

        let impl_ast = Impl {
            ty: parsed_impl_ty,
            qualifiers: vec![],
            externs: None,
            funcs: Some(vec![method_decl]),
            consts: None,
            is_object: false,
        };

        impl_decl = Node::new(Decl::Impl(impl_ast));
        impl_root_node = impl_decl.id;
        source_map.set_src(&impl_decl, src.clone());
        source_map.mark_synthetic(impl_root_node);
    }

    defs.push(DefHeader {
        def_id: impl_def_id,
        root_node: impl_root_node,
        name: trait_name.to_string(),
        kind: DefKind::Impl,
        span: Span::default(),
        name_span: Span::default(),
        parent: None,
    });

    defs.push(DefHeader {
        def_id: method_def_id,
        root_node: method_root_node,
        name: method_name.to_string(),
        kind: DefKind::Method,
        span: Span::default(),
        name_span: Span::default(),
        parent: Some(impl_def_id),
    });

    synthetic_defs.insert(impl_def_id);
    synthetic_defs.insert(method_def_id);

    decls.push(impl_decl);
}

/// Builds a Clone method: `fn clone(self: *StructTy) -> StructTy => StructName { f1: self.f1, ... }`
///
/// Returns `(method_name, method_decl, method_root_node)`.
fn build_clone_method(
    method_def_id: DefId,
    struct_ast: &Struct,
    struct_ty: &Ty,
    src: &Source,
    source_map: &mut SourceMap,
) -> (&'static str, Node<Decl>, NodeId) {
    let self_ty = Ty::Ref(Box::new(struct_ty.clone()));

    let method_decl;
    let method_root_node;
    {
        let _method_guard = NodeId::enter_def(method_def_id);

        let fields = struct_ast
            .fields
            .as_ref()
            .map(|f| f.as_slice())
            .unwrap_or(&[]);

        let elements: Vec<Node<CurlyElement>> = fields
            .iter()
            .map(|field_node| {
                let field_name = field_node.value.path.name().unwrap_or_default();

                // self.field_name
                let self_node = Node::new(Expr::Name(Name::new("self")));
                source_map.set_src(&self_node, src.clone());
                source_map.mark_synthetic(self_node.id);

                let rhs_name = Node::new(Name::new(&field_name));
                source_map.set_src(&rhs_name, src.clone());
                source_map.mark_synthetic(rhs_name.id);

                let dot_node = Node::new(Expr::Dot(Dot {
                    lhs: Box::new(self_node),
                    rhs: rhs_name,
                    dot: Token::new(TokenKind::Dot),
                }));
                source_map.set_src(&dot_node, src.clone());
                source_map.mark_synthetic(dot_node.id);

                let elem = Node::new(CurlyElement::Labeled(Name::new(&field_name), dot_node));
                source_map.set_src(&elem, src.clone());
                source_map.mark_synthetic(elem.id);

                elem
            })
            .collect();

        // StructName { f1: self.f1, f2: self.f2, ... }
        let struct_path_node = Node::new(struct_ast.path.value.clone());
        source_map.set_src(&struct_path_node, src.clone());
        source_map.mark_synthetic(struct_path_node.id);

        let body = Node::new(Expr::Curly(Curly {
            lhs: Some(struct_path_node),
            elements,
            curly_span: Span::default(),
            ty: TyScheme::default(),
        }));
        source_map.set_src(&body, src.clone());
        source_map.mark_synthetic(body.id);

        // fn clone(self: *StructTy) -> StructTy => <body>
        let sig_path = Node::new(Path::from("clone"));
        source_map.set_src(&sig_path, src.clone());
        source_map.mark_synthetic(sig_path.id);

        // Self param type: *StructTy
        let self_ty_mono = self_ty.clone();
        let self_ty_ids = make_synthetic_ids(&self_ty_mono, source_map, src);
        let mut parsed_self_ty = Parsed::new(TyScheme::from_mono(self_ty), src.clone());
        parsed_self_ty.set_synthetic_ids(self_ty_ids);

        let self_param = Node::new(FnParam::Name {
            name: Name::typed("self", parsed_self_ty),
            is_move: false,
            is_noescape: false,
            receiver: None,
        });
        source_map.set_src(&self_param, src.clone());
        source_map.mark_synthetic(self_param.id);

        // Return type: StructTy
        let ret_ty_ids = make_synthetic_ids(struct_ty, source_map, src);
        let mut parsed_ret_ty = Parsed::new(struct_ty.clone(), src.clone());
        parsed_ret_ty.set_synthetic_ids(ret_ty_ids);

        let func = Func {
            sig: FuncSig {
                path: sig_path,
                params: vec![self_param],
                ty_params: None,
                ret_ty: Some(parsed_ret_ty),
                ty: None,
                modifiers: vec![],
                qualifiers: vec![],
                doc_comment: None,
                is_anon: false,
                is_method: true,
                has_body: true,
                span: Span::default(),
            },
            body: Some(Box::new(body)),
        };

        method_decl = Node::new(Decl::Func(func));
        method_root_node = method_decl.id;
        source_map.set_src(&method_decl, src.clone());
        source_map.mark_synthetic(method_root_node);
    }

    ("clone", method_decl, method_root_node)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ray_shared::{
        def::DefKind,
        file_id::FileId,
        pathlib::{FilePath, ModulePath},
    };

    use crate::{
        queries::{
            auto_derive::auto_derive_impls,
            libraries::LoadedLibraries,
            parse::{parse_file, parse_file_raw},
            workspace::{FileMetadata, FileSource, WorkspaceSnapshot},
        },
        query::Database,
    };

    const CLONE_TRAIT: &str = r#"
        trait Clone['a] {
            fn clone(self: *'a) -> 'a
        }
    "#;

    fn setup_db(source: &str) -> (Database, FileId) {
        let db = Database::new();
        let mut workspace = WorkspaceSnapshot::new();
        let module_path = ModulePath::from("test");
        let file_id = workspace.add_file(FilePath::from("test/mod.ray"), module_path.clone());
        db.set_input::<WorkspaceSnapshot>((), workspace);
        LoadedLibraries::new(&db, (), HashMap::new(), HashMap::new());
        FileSource::new(&db, file_id, source.to_string());
        FileMetadata::new(&db, file_id, FilePath::from("test/mod.ray"), module_path);
        (db, file_id)
    }

    fn with_clone_trait(source: &str) -> String {
        format!("{CLONE_TRAIT}\n\n{source}")
    }

    #[test]
    fn no_synthetic_impls_when_clone_not_in_scope() {
        let (db, file_id) = setup_db("struct Foo { x: int }");
        let result = auto_derive_impls(&db, file_id);
        assert!(
            result.defs.is_empty(),
            "no Clone in scope → no synthetic impls"
        );
    }

    #[test]
    fn synthesizes_clone_impl_for_struct() {
        let source = with_clone_trait("struct Foo { x: int }");
        let (db, file_id) = setup_db(&source);
        let result = auto_derive_impls(&db, file_id);

        let impl_defs: Vec<_> = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Impl))
            .collect();
        let method_defs: Vec<_> = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Method))
            .collect();
        assert_eq!(impl_defs.len(), 1, "one synthetic impl");
        assert_eq!(method_defs.len(), 1, "one synthetic method");
        assert_eq!(method_defs[0].name, "clone");

        for def in &result.defs {
            assert!(
                result.synthetic_defs.contains(&def.def_id),
                "all defs should be marked synthetic"
            );
        }
    }

    #[test]
    fn no_synthetic_clone_when_explicit_impl_exists() {
        let source = with_clone_trait(
            r#"
struct Foo { x: int }

impl Clone[Foo] {
    fn clone(self: *Foo) -> Foo => Foo { x: self.x }
}
"#,
        );
        let (db, file_id) = setup_db(&source);
        let result = auto_derive_impls(&db, file_id);
        assert!(result.defs.is_empty(), "explicit Clone impl → no synthetic");
    }

    #[test]
    fn synthesizes_clone_for_multiple_structs() {
        let source = with_clone_trait(
            r#"
struct Foo { x: int }
struct Bar { y: int, z: int }
"#,
        );
        let (db, file_id) = setup_db(&source);
        let result = auto_derive_impls(&db, file_id);

        let impl_count = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Impl))
            .count();
        assert_eq!(impl_count, 2, "one synthetic impl per struct");
    }

    #[test]
    fn explicit_impl_only_suppresses_that_struct() {
        let source = with_clone_trait(
            r#"
struct Foo { x: int }
struct Bar { y: int }

impl Clone[Foo] {
    fn clone(self: *Foo) -> Foo => Foo { x: self.x }
}
"#,
        );
        let (db, file_id) = setup_db(&source);
        let result = auto_derive_impls(&db, file_id);

        let impl_count = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Impl))
            .count();
        assert_eq!(impl_count, 1, "only Bar should get synthetic Clone");
    }

    #[test]
    fn parse_file_raw_has_no_synthetic_defs() {
        let source = with_clone_trait("struct Foo { x: int }");
        let (db, file_id) = setup_db(&source);
        let raw = parse_file_raw(&db, file_id);
        assert!(
            raw.synthetic_defs.is_empty(),
            "raw parse has no synthetic defs"
        );
    }

    #[test]
    fn parse_file_merges_synthetic_impls() {
        let source = with_clone_trait("struct Foo { x: int }");
        let (db, file_id) = setup_db(&source);
        let raw = parse_file_raw(&db, file_id);
        let merged = parse_file(&db, file_id);

        assert!(
            merged.defs.len() > raw.defs.len(),
            "parse_file should merge synthetic defs: raw={}, merged={}",
            raw.defs.len(),
            merged.defs.len()
        );
        assert!(
            !merged.synthetic_defs.is_empty(),
            "synthetic defs should be populated"
        );
    }

    #[test]
    fn synthesizes_clone_for_generic_struct_with_ref_field() {
        let source = with_clone_trait("struct Foo['a] { value: *'a }");
        let (db, file_id) = setup_db(&source);
        let result = auto_derive_impls(&db, file_id);

        let impl_defs: Vec<_> = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Impl))
            .collect();
        let method_defs: Vec<_> = result
            .defs
            .iter()
            .filter(|d| matches!(d.kind, DefKind::Method))
            .collect();
        assert_eq!(impl_defs.len(), 1, "one synthetic impl");
        assert_eq!(method_defs.len(), 1, "one synthetic clone method");
        assert_eq!(method_defs[0].name, "clone");
    }
}
