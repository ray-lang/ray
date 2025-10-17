use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::{
    ast::{Decl, Func, Module, Node, Path},
    lir,
    pathlib::FilePath,
    sema::NameContext,
    span::{SourceMap, Span},
    typing::{TyCtx, state::SchemeEnv},
};

#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub program: lir::Program,
    pub tcx: TyCtx,
    pub ncx: NameContext,
    pub srcmap: SourceMap,
    pub defs: SchemeEnv,
    pub modules: Vec<Path>,
    pub definitions: HashMap<String, DefinitionRecord>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinitionRecord {
    pub id: u64,
    pub display_path: String,
    pub file: Option<FilePath>,
    pub span: Option<Span>,
    pub doc: Option<String>,
}

pub fn serialize(
    program: lir::Program,
    tcx: TyCtx,
    ncx: NameContext,
    srcmap: SourceMap,
    defs: SchemeEnv,
    modules: Vec<Path>,
    definitions: HashMap<String, DefinitionRecord>,
) -> Vec<u8> {
    bincode::serialize(&RayLib {
        program,
        tcx,
        ncx,
        srcmap,
        defs,
        modules,
        definitions,
    })
    .unwrap()
}

pub fn collect_definition_records(
    module: &Module<(), Decl>,
    srcmap: &SourceMap,
) -> HashMap<String, DefinitionRecord> {
    let mut records = HashMap::new();
    for decl in &module.decls {
        register_decl_paths(decl, srcmap, &mut records);
    }
    records
}

pub fn canonical_path_key(path: &Path) -> String {
    let mut tyvar_map = HashMap::new();
    let mut counter = 0usize;

    path.to_vec()
        .into_iter()
        .filter_map(|segment| {
            if is_type_args_segment(segment) {
                None
            } else {
                Some(normalize_tyvars_in_segment(
                    segment,
                    &mut tyvar_map,
                    &mut counter,
                ))
            }
        })
        .collect::<Vec<_>>()
        .join("::")
}

pub fn display_path(path: &Path) -> String {
    let mut tyvar_map = HashMap::new();
    let mut counter = 0usize;

    path.to_vec()
        .into_iter()
        .map(|segment| normalize_tyvars_in_segment(segment, &mut tyvar_map, &mut counter))
        .collect::<Vec<_>>()
        .join("::")
}

fn register_decl_paths(
    decl: &Node<Decl>,
    srcmap: &SourceMap,
    records: &mut HashMap<String, DefinitionRecord>,
) {
    match &decl.value {
        Decl::Func(func) => {
            insert_definition_record(records, &func.sig.path, decl.id, srcmap);
        }
        Decl::FnSig(sig) => {
            insert_definition_record(records, &sig.path, decl.id, srcmap);
        }
        Decl::Extern(ext) => {
            register_decl_paths(ext.decl_node(), srcmap, records);
        }
        Decl::Trait(tr) => {
            insert_definition_record_with_string(records, &tr.ty.to_string(), decl.id, srcmap);
            for field in &tr.fields {
                register_decl_paths(field, srcmap, records);
            }
        }
        Decl::Impl(im) => {
            if let Some(funcs) = &im.funcs {
                for func in funcs {
                    register_func_paths(func, srcmap, records);
                }
            }

            if let Some(externs) = &im.externs {
                for ext in externs {
                    register_decl_paths(ext, srcmap, records);
                }
            }
        }
        Decl::TypeAlias(name, _) => {
            insert_definition_record(records, &name.value.path, decl.id, srcmap);
        }
        _ => {}
    }
}

fn register_func_paths(
    func: &Node<Func>,
    srcmap: &SourceMap,
    records: &mut HashMap<String, DefinitionRecord>,
) {
    insert_definition_record(records, &func.sig.path, func.id, srcmap);
}

fn insert_definition_record(
    records: &mut HashMap<String, DefinitionRecord>,
    path: &Path,
    id: u64,
    srcmap: &SourceMap,
) {
    let key = canonical_path_key(path);
    let display_path = display_path(path);
    let source = srcmap.get_by_id(id);
    let (file, span, doc) = source
        .map(|src| {
            (
                Some(src.filepath.clone()),
                src.span,
                srcmap.doc_by_id(id).cloned(),
            )
        })
        .unwrap_or((None, None, None));
    records.entry(key).or_insert(DefinitionRecord {
        id,
        display_path,
        file,
        span,
        doc,
    });
}

fn insert_definition_record_with_string(
    records: &mut HashMap<String, DefinitionRecord>,
    path_str: &str,
    id: u64,
    srcmap: &SourceMap,
) {
    let source = srcmap.get_by_id(id);
    let (file, span, doc) = source
        .map(|src| {
            (
                Some(src.filepath.clone()),
                src.span,
                srcmap.doc_by_id(id).cloned(),
            )
        })
        .unwrap_or((None, None, None));
    records
        .entry(path_str.to_string())
        .or_insert(DefinitionRecord {
            id,
            display_path: path_str.to_string(),
            file,
            span,
            doc,
        });
}

fn normalize_tyvars_in_segment(
    segment: &str,
    tyvar_map: &mut HashMap<String, String>,
    counter: &mut usize,
) -> String {
    let mut out = String::new();
    let mut chars = segment.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '?' {
            if let Some(&next) = chars.peek() {
                if next == 't' {
                    chars.next();
                    let mut var = String::from("?t");
                    while let Some(&peek) = chars.peek() {
                        if peek.is_ascii_alphanumeric() || peek == '_' {
                            var.push(peek);
                            chars.next();
                        } else {
                            break;
                        }
                    }

                    let pretty = tyvar_map.entry(var.clone()).or_insert_with(|| {
                        let name = pretty_tyvar_name(*counter);
                        *counter += 1;
                        name
                    });
                    out.push_str(pretty.as_str());
                    continue;
                }
            }
        }

        out.push(ch);
    }

    out
}

fn is_type_args_segment(segment: &str) -> bool {
    segment.starts_with('[') && segment.ends_with(']')
}

fn pretty_tyvar_name(index: usize) -> String {
    let letter = (b'a' + (index % 26) as u8) as char;
    let suffix = index / 26;
    if suffix == 0 {
        format!("'{}", letter)
    } else {
        format!("'{}{}", letter, suffix)
    }
}
