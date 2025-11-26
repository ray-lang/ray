use std::{
    collections::{HashMap, VecDeque},
    fmt::Display,
};

use ray_shared::{
    collections::namecontext::NameContext,
    pathlib::{FilePath, Path, PathPart},
    span::Span,
};
use ray_typing::{TyCtx, state::SchemeEnv, ty::Ty};
use serde::{Deserialize, Serialize};

use crate::{
    ast::{CurlyElement, Decl, Expr, FnParam, Func, FuncSig, Modifier, Module, Node, Pattern},
    lir,
    sourcemap::SourceMap,
};

#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub program: lir::Program,
    pub tcx: TyCtx,
    pub ncx: NameContext,
    pub srcmap: SourceMap,
    pub defs: SchemeEnv,
    pub modules: Vec<Path>,
    pub definitions: HashMap<Path, DefinitionRecord>,
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
    Extern,
    TypeAlias,
    Unknown,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinitionRecord {
    pub id: u64,
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
                DefinitionKind::Extern | DefinitionKind::TypeAlias => Ok(()),
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

pub fn serialize(
    program: lir::Program,
    tcx: TyCtx,
    ncx: NameContext,
    srcmap: SourceMap,
    defs: SchemeEnv,
    modules: Vec<Path>,
    definitions: HashMap<Path, DefinitionRecord>,
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
    tcx: &TyCtx,
) -> HashMap<Path, DefinitionRecord> {
    let mut records = HashMap::new();
    for decl in &module.decls {
        register_decl_paths(decl, srcmap, tcx, &mut records, None);
    }
    records
}

pub fn canonical_path_key(path: &Path) -> Path {
    let mut tyvar_map = HashMap::new();
    let mut counter = 0usize;

    path.iter()
        .filter_map(|segment| match segment {
            PathPart::Name(name) => {
                let normalized = normalize_tyvars_in_segment(name, &mut tyvar_map, &mut counter);
                Some(PathPart::Name(normalized))
            }
            PathPart::FuncType(ty) => {
                let normalized = normalize_tyvars_in_segment(ty, &mut tyvar_map, &mut counter);
                Some(PathPart::FuncType(normalized))
            }
            PathPart::TypeArgs(args) => {
                let normalized = normalize_tyvars_in_segment(args, &mut tyvar_map, &mut counter);
                Some(PathPart::TypeArgs(normalized))
            }
        })
        .collect::<VecDeque<_>>()
        .into()
}

pub fn display_path(path: &Path) -> Path {
    let mut tyvar_map = HashMap::new();
    let mut counter = 0usize;

    path.iter()
        .map(|segment| match segment {
            PathPart::Name(name) => {
                let normalized = normalize_tyvars_in_segment(name, &mut tyvar_map, &mut counter);
                PathPart::Name(normalized)
            }
            PathPart::TypeArgs(ty) => {
                let normalized = normalize_tyvars_in_segment(ty, &mut tyvar_map, &mut counter);
                PathPart::TypeArgs(normalized)
            }
            PathPart::FuncType(ty) => {
                let normalized = normalize_tyvars_in_segment(ty, &mut tyvar_map, &mut counter);
                PathPart::FuncType(normalized)
            }
        })
        .collect::<VecDeque<_>>()
        .into()
}

fn register_decl_paths(
    decl: &Node<Decl>,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
    parent: Option<&DefinitionKind>,
) {
    match &decl.value {
        Decl::Func(func) => {
            register_func(decl.id, func, srcmap, tcx, records, parent);
        }
        Decl::FnSig(sig) => {
            register_func_sig(decl.id, sig, srcmap, tcx, records, parent);
        }
        Decl::Extern(ext) => {
            let parent = DefinitionKind::Extern;
            register_decl_paths(ext.decl_node(), srcmap, tcx, records, Some(&parent));
        }
        Decl::Trait(tr) => {
            let kind = DefinitionKind::Trait {
                ty: tcx.pretty_tys(tr.ty.value()),
            };

            for field in &tr.fields {
                register_decl_paths(field, srcmap, tcx, records, Some(&kind));
            }

            insert_definition_record(records, &*tr.path, decl.id, srcmap, kind);
        }
        Decl::Impl(im) => {
            let kind = DefinitionKind::Impl {
                ty: tcx.pretty_tys(im.ty.value()),
                qualifiers: im
                    .qualifiers
                    .iter()
                    .map(|t| tcx.pretty_tys(t.value()))
                    .collect(),
            };

            if let Some(funcs) = &im.funcs {
                for func in funcs {
                    register_func(func.id, func, srcmap, tcx, records, Some(&kind));
                }
            }

            if let Some(externs) = &im.externs {
                for ext in externs {
                    register_decl_paths(ext, srcmap, tcx, records, Some(&kind));
                }
            }

            insert_definition_record(records, &im.ty.get_path(), decl.id, srcmap, kind);
        }
        Decl::Struct(st) => {
            let kind = DefinitionKind::Struct {
                path: st.path.value.clone(),
                type_params: st.ty_params.as_ref().map(|tps| {
                    tps.tys
                        .iter()
                        .map(|tp| tcx.pretty_tys(tp.value()))
                        .collect()
                }),
            };

            if let Some(fields) = &st.fields {
                for field in fields {
                    let field_path = st.path.append_path(field.value.path.clone());
                    insert_definition_record(
                        records,
                        &field_path,
                        field.id,
                        srcmap,
                        DefinitionKind::Name {
                            ty: field.ty.as_ref().map(|t| tcx.pretty_tys(t.mono())),
                            parent: Some(Box::new(kind.clone())),
                        },
                    );
                }
            }

            insert_definition_record(records, &st.path.value, decl.id, srcmap, kind);
        }
        Decl::TypeAlias(name, _) => {
            insert_definition_record(
                records,
                &name.value.path,
                decl.id,
                srcmap,
                DefinitionKind::TypeAlias,
            );
        }
        Decl::Mutable(_) => todo!(),
        Decl::Name(_) => todo!(),
        Decl::Declare(_) => todo!(),
    }
}

fn register_fn_params(
    params: &Vec<Node<FnParam>>,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
) {
    for param in params {
        register_fn_param(param, srcmap, tcx, records);
    }
}

fn register_fn_param(
    param: &Node<FnParam>,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
) {
    match &param.value {
        FnParam::Name(name) => {
            insert_definition_record(
                records,
                &name.path,
                param.id,
                srcmap,
                DefinitionKind::Name {
                    ty: name.ty.as_ref().map(|t| tcx.pretty_tys(t.mono())),
                    parent: None,
                },
            );
        }
        FnParam::DefaultValue(param, _) => {
            register_fn_param(param, srcmap, tcx, records);
        }
        FnParam::Missing { .. } => {}
    }
}

fn register_func(
    id: u64,
    func: &Func,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
    parent: Option<&DefinitionKind>,
) {
    let kind = func_sig_kind(&func.sig, parent);

    register_fn_params(&func.sig.params, srcmap, tcx, records);

    if let Some(body) = &func.body {
        register_in_expr(body, srcmap, tcx, records, Some(&kind));
    }

    insert_definition_record(records, &*func.sig.path, id, srcmap, kind);
}

fn register_func_sig(
    id: u64,
    sig: &FuncSig,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
    parent: Option<&DefinitionKind>,
) {
    register_fn_params(&sig.params, srcmap, tcx, records);

    let kind = func_sig_kind(sig, parent);
    insert_definition_record(records, &*sig.path, id, srcmap, kind);
}

fn register_in_expr(
    expr: &Node<Expr>,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
    parent: Option<&DefinitionKind>,
) {
    match &expr.value {
        Expr::Assign(assign) => {
            register_in_pattern(&assign.lhs, srcmap, tcx, records);
            register_in_expr(&assign.rhs, srcmap, tcx, records, parent);
        }
        Expr::BinOp(bin_op) => {
            register_in_expr(&bin_op.lhs, srcmap, tcx, records, parent);
            register_in_expr(&bin_op.rhs, srcmap, tcx, records, parent);
        }
        Expr::Block(block) => {
            for stmt in &block.stmts {
                register_in_expr(stmt, srcmap, tcx, records, parent);
            }
        }
        Expr::Boxed(boxed) => {
            register_in_expr(&boxed.inner, srcmap, tcx, records, parent);
        }
        Expr::Break(node) => {
            if let Some(expr) = node {
                register_in_expr(&expr, srcmap, tcx, records, parent);
            }
        }
        Expr::Call(call) => {
            register_in_expr(&call.callee, srcmap, tcx, records, parent);
            for arg in call.args.items.iter() {
                register_in_expr(arg, srcmap, tcx, records, parent);
            }
        }
        Expr::Cast(cast) => {
            register_in_expr(&cast.lhs, srcmap, tcx, records, parent);
        }
        Expr::Closure(closure) => {
            for param in closure.args.items.iter() {
                register_in_expr(&param, srcmap, tcx, records, parent);
            }
            register_in_expr(&closure.body, srcmap, tcx, records, parent);
        }
        Expr::Curly(curly) => {
            for field in curly.elements.iter() {
                match &field.value {
                    CurlyElement::Name(_) => continue,
                    CurlyElement::Labeled(_, node) => {
                        register_in_expr(&node, srcmap, tcx, records, parent);
                    }
                }
            }
        }
        Expr::Deref(deref) => {
            register_in_expr(&deref.expr, srcmap, tcx, records, parent);
        }
        Expr::Dot(dot) => {
            register_in_expr(&dot.lhs, srcmap, tcx, records, parent);
        }
        Expr::Func(func) => {
            insert_definition_record(
                records,
                &*func.sig.path,
                expr.id,
                srcmap,
                func_sig_kind(&func.sig, parent),
            );
            if let Some(body) = &func.body {
                register_in_expr(body, srcmap, tcx, records, parent);
            }
        }
        Expr::For(fr) => {
            register_in_pattern(&fr.pat, srcmap, tcx, records);
            register_in_expr(&fr.expr, srcmap, tcx, records, parent);
            register_in_expr(&fr.body, srcmap, tcx, records, parent);
        }
        Expr::If(i) => {
            register_in_expr(&i.cond, srcmap, tcx, records, parent);
            register_in_expr(&i.then, srcmap, tcx, records, parent);
            if let Some(els) = &i.els {
                register_in_expr(els, srcmap, tcx, records, parent);
            }
        }
        Expr::Index(index) => {
            register_in_expr(&index.lhs, srcmap, tcx, records, parent);
            register_in_expr(&index.index, srcmap, tcx, records, parent);
        }
        Expr::Labeled(_, expr) => {
            register_in_expr(&expr, srcmap, tcx, records, parent);
        }
        Expr::List(list) => {
            for item in list.items.iter() {
                register_in_expr(item, srcmap, tcx, records, parent);
            }
        }
        Expr::Loop(l) => {
            register_in_expr(&l.body, srcmap, tcx, records, parent);
        }
        Expr::Paren(node) => {
            register_in_expr(&node, srcmap, tcx, records, parent);
        }
        Expr::Range(range) => {
            register_in_expr(&range.start, srcmap, tcx, records, parent);
            register_in_expr(&range.end, srcmap, tcx, records, parent);
        }
        Expr::Ref(rf) => {
            register_in_expr(&rf.expr, srcmap, tcx, records, parent);
        }
        Expr::Return(node) => {
            if let Some(expr) = node {
                register_in_expr(&expr, srcmap, tcx, records, parent);
            }
        }
        Expr::Sequence(sequence) => {
            for item in sequence.items.iter() {
                register_in_expr(item, srcmap, tcx, records, parent);
            }
        }
        Expr::Tuple(tuple) => {
            for elem in tuple.seq.items.iter() {
                register_in_expr(elem, srcmap, tcx, records, parent);
            }
        }
        Expr::Some(inner) => {
            register_in_expr(&inner, srcmap, tcx, records, parent);
        }
        Expr::TypeAnnotated(node, _) => {
            register_in_expr(&node, srcmap, tcx, records, parent);
        }
        Expr::UnaryOp(unary_op) => {
            register_in_expr(&unary_op.expr, srcmap, tcx, records, parent);
        }
        Expr::Unsafe(node) => {
            register_in_expr(&node, srcmap, tcx, records, parent);
        }
        Expr::While(w) => {
            register_in_expr(&w.cond, srcmap, tcx, records, parent);
            register_in_expr(&w.body, srcmap, tcx, records, parent);
        }

        // ignore
        Expr::DefaultValue(_)
        | Expr::Literal(_)
        | Expr::Missing(_)
        | Expr::Name(_)
        | Expr::New(_)
        | Expr::Path(_)
        | Expr::Pattern(_)
        | Expr::Type(_) => {}
    }
}

fn register_in_pattern(
    pattern: &Node<Pattern>,
    srcmap: &SourceMap,
    tcx: &TyCtx,
    records: &mut HashMap<Path, DefinitionRecord>,
) {
    match &pattern.value {
        Pattern::Name(name) => {
            let resolved_ty = tcx.pretty_tys(&tcx.get_ty(pattern.id).cloned());
            insert_definition_record(
                records,
                &name.path,
                pattern.id,
                srcmap,
                DefinitionKind::Name {
                    ty: resolved_ty,
                    parent: None,
                },
            );
        }
        Pattern::Tuple(elems) => {
            for elem in elems.iter() {
                register_in_pattern(elem, srcmap, tcx, records);
            }
        }
        Pattern::Sequence(nodes) => {
            for node in nodes.iter() {
                register_in_pattern(node, srcmap, tcx, records);
            }
        }
        Pattern::Some(pattern) => register_in_pattern(pattern, srcmap, tcx, records),
        Pattern::Deref(_) | Pattern::Dot(_, _) | Pattern::Missing(_) => {
            // ignore
        }
    }
}

fn insert_definition_record(
    records: &mut HashMap<Path, DefinitionRecord>,
    path: &Path,
    id: u64,
    srcmap: &SourceMap,
    kind: DefinitionKind,
) {
    let key = canonical_path_key(path);
    let display_path = display_path(path);
    let source = srcmap.get_by_id(id);
    let doc = source.as_ref().and_then(|_| srcmap.doc_by_id(id).cloned());
    let (file, span) = source
        .map(|src| (Some(src.filepath), src.span))
        .unwrap_or((None, None));

    records.entry(key).or_insert(DefinitionRecord {
        id,
        display_path,
        file,
        span,
        doc,
        kind,
    });
}

fn func_sig_kind(sig: &FuncSig, parent: Option<&DefinitionKind>) -> DefinitionKind {
    DefinitionKind::Function {
        params: sig
            .params
            .iter()
            .map(|param| (param.name().clone(), param.ty().cloned()))
            .collect(),
        return_ty: sig.ret_ty.as_ref().map(|t| t.clone_value()),
        type_params: sig.ty_params.as_ref().map(|tps| {
            tps.tys
                .iter()
                .map(|tp| tp.clone_value())
                .collect::<Vec<Ty>>()
        }),
        modifiers: sig.modifiers.clone(),
        qualifiers: sig.qualifiers.iter().map(|t| t.clone_value()).collect(),
        parent: parent.cloned().map(Box::new),
    }
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

fn pretty_tyvar_name(index: usize) -> String {
    let letter = (b'a' + (index % 26) as u8) as char;
    let suffix = index / 26;
    if suffix == 0 {
        format!("'{}", letter)
    } else {
        format!("'{}{}", letter, suffix)
    }
}
