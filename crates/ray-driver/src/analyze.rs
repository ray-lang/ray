use std::{cmp::Ordering, collections::HashSet, ffi::OsString, str::FromStr};

use clap::Args;
use ray_core::{
    ast::{Decl, Node},
    errors::RayError,
    sourcemap::SourceMap,
};
use ray_frontend::{
    queries::{
        defs::def_path,
        locations::span_of,
        parse::parse_file,
        resolve::name_resolutions,
        symbols::symbol_targets,
        typecheck::{def_scheme, ty_of},
        workspace::WorkspaceSnapshot,
    },
    query::Database,
};
use ray_shared::{
    node_id::NodeId,
    pathlib::{FilePath, ItemPath},
    resolution::DefTarget,
    span::{Pos, Source, Span},
    symbol::{SymbolIdentity, SymbolRole},
};

use crate::GlobalOptions;

#[derive(Debug, Clone, Copy)]
pub enum AnalysisFormat {
    Text,
    Json,
}

impl AnalysisFormat {
    pub fn as_str(&self) -> &'static str {
        match self {
            AnalysisFormat::Text => "text",
            AnalysisFormat::Json => "json",
        }
    }
}

impl std::fmt::Display for AnalysisFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnalysisFormat::Text => write!(f, "text"),
            AnalysisFormat::Json => write!(f, "json"),
        }
    }
}

impl FromStr for AnalysisFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_ascii_lowercase().as_str() {
            "text" => Ok(AnalysisFormat::Text),
            "json" => Ok(AnalysisFormat::Json),
            other => Err(format!(
                "invalid analysis format `{}` (expected `text` or `json`)",
                other
            )),
        }
    }
}

fn parse_analysis_format(input: &str) -> Result<AnalysisFormat, String> {
    AnalysisFormat::from_str(input)
}

#[derive(Debug, Args)]
pub struct AnalyzeOptions {
    #[arg(value_name = "INPUT", help = "Ray source file to analyze")]
    pub input_path: FilePath,

    #[arg(
        long = "format",
        default_value = "text",
        value_parser = parse_analysis_format,
        help = "Output format (text or json)"
    )]
    pub format: AnalysisFormat,

    #[arg(
        long = "no-core",
        default_value = "false",
        help = "Disable automatic import of `core` library",
        action = clap::ArgAction::SetTrue
    )]
    pub no_core: bool,
}

impl AnalyzeOptions {
    pub fn to_argv(self, globals: GlobalOptions) -> Vec<OsString> {
        let mut args = vec![];

        if let Some(root_path) = globals.root_path {
            args.push("--root-path".into());
            args.push(root_path.to_string().into());
        }

        if let Some(config_path) = globals.config_path {
            args.push("--config-path".into());
            args.push(config_path.to_string().into());
        }

        args.push("--log-level".into());
        args.push(globals.log_level.to_string().into());

        args.push("--format".into());
        args.push(self.format.to_string().into());

        if self.no_core {
            args.push("--no-core".into());
        }

        args
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisStatus {
    Ok,
    Errors,
}

impl AnalysisStatus {
    fn as_str(&self) -> &'static str {
        match self {
            AnalysisStatus::Ok => "ok",
            AnalysisStatus::Errors => "errors",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    Function,
    Struct,
    Trait,
    TypeAlias,
    Field, // Added to represent struct fields
}

impl SymbolKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            SymbolKind::Function => "function",
            SymbolKind::Struct => "struct",
            SymbolKind::Trait => "trait",
            SymbolKind::TypeAlias => "type_alias",
            SymbolKind::Field => "field", // Added string representation for Field
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub id: NodeId,
    pub name: String,
    pub kind: SymbolKind,
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub ty: Option<String>,
    pub parent_id: Option<NodeId>,
    pub doc: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub id: NodeId,
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub ty: String,
    pub is_scheme: bool,
}

#[derive(Debug, Clone)]
pub struct DefinitionInfo {
    pub usage_id: NodeId,
    pub usage_path: ItemPath,
    pub usage_filepath: FilePath,
    pub usage_span: Option<Span>,
    pub definition_id: Option<NodeId>,
    pub definition_path: Option<ItemPath>,
    pub definition_filepath: Option<FilePath>,
    pub definition_span: Option<Span>,
    pub definition_doc: Option<String>,
}

#[derive(Debug)]
pub struct AnalysisReport {
    pub format: AnalysisFormat,
    pub input_path: FilePath,
    pub module_path: ray_shared::pathlib::Path,
    pub diagnostics: Vec<RayError>,
    pub symbols: Vec<SymbolInfo>,
    pub types: Vec<TypeInfo>,
    pub definitions: Vec<DefinitionInfo>,
}

impl AnalysisReport {
    pub fn new(
        format: AnalysisFormat,
        input_path: FilePath,
        module_path: ray_shared::pathlib::Path,
        diagnostics: Vec<RayError>,
        symbols: Vec<SymbolInfo>,
        types: Vec<TypeInfo>,
        definitions: Vec<DefinitionInfo>,
    ) -> Self {
        Self {
            format,
            input_path,
            module_path,
            diagnostics,
            symbols,
            types,
            definitions,
        }
    }

    pub fn status(&self) -> AnalysisStatus {
        if self.diagnostics.is_empty() {
            AnalysisStatus::Ok
        } else {
            AnalysisStatus::Errors
        }
    }

    pub fn emit(self) {
        match self.format {
            AnalysisFormat::Text => self.emit_text(),
            AnalysisFormat::Json => self.emit_json(),
        }
    }

    fn emit_text(self) {
        let status = self.status();
        let AnalysisReport {
            format: _,
            input_path,
            module_path,
            diagnostics,
            symbols,
            types,
            definitions,
        } = self;

        match status {
            AnalysisStatus::Ok => println!("analysis ok: {}", input_path),
            AnalysisStatus::Errors => {
                println!(
                    "analysis found {} diagnostic(s) in {}",
                    diagnostics.len(),
                    input_path
                );
            }
        }

        for err in diagnostics {
            emit_text_diagnostic(err);
        }

        if !module_path.is_empty() {
            println!("module path: {}", module_path);
        }

        if !symbols.is_empty() {
            println!("symbols ({}):", symbols.len());
            for symbol in &symbols {
                emit_text_symbol(symbol);
            }
        }

        if !types.is_empty() {
            println!("types ({} entries)", types.len());
        }

        if !definitions.is_empty() {
            println!("definitions ({} entries)", definitions.len());
            for def in &definitions {
                emit_text_definition(def);
            }
        }
    }

    fn emit_json(self) {
        let status = self.status();
        let AnalysisReport {
            format: _,
            input_path,
            module_path,
            diagnostics,
            symbols,
            types,
            definitions,
        } = self;

        let diagnostics = diagnostics
            .into_iter()
            .map(diagnostic_to_json)
            .collect::<Vec<_>>()
            .join(",");
        let symbols = symbols
            .into_iter()
            .map(symbol_to_json)
            .collect::<Vec<_>>()
            .join(",");
        let types = types
            .into_iter()
            .map(type_to_json)
            .collect::<Vec<_>>()
            .join(",");
        let definitions = definitions
            .into_iter()
            .map(definition_to_json)
            .collect::<Vec<_>>()
            .join(",");

        println!(
            "{{\"status\":\"{}\",\"input\":\"{}\",\"module_path\":\"{}\",\"diagnostics\":[{}],\"symbols\":[{}],\"types\":[{}],\"definitions\":[{}]}}",
            status.as_str(),
            escape_json(&input_path.to_string()),
            module_path,
            diagnostics,
            symbols,
            types,
            definitions
        );
    }
}

fn diagnostic_to_json(err: RayError) -> String {
    let kind = escape_json(&err.kind.to_string());
    let message = escape_json(&err.msg);
    let sources = err
        .src
        .into_iter()
        .map(source_to_json)
        .collect::<Vec<_>>()
        .join(",");

    format!(
        "{{\"kind\":\"{}\",\"message\":\"{}\",\"sources\":[{}]}}",
        kind, message, sources
    )
}

fn escape_json(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn emit_text_diagnostic(err: RayError) {
    eprintln!("{}: {}", err.kind, err.msg);
    for src in err.src {
        emit_text_source(&src);
    }
}

fn emit_text_source(src: &Source) {
    if let Some(span) = src.span {
        eprintln!(
            "  --> {}:{}:{}",
            src.filepath,
            span.start.lineno + 1,
            span.start.col + 1
        );
    } else {
        eprintln!("  --> {}", src.filepath);
    }
}

fn emit_text_symbol(symbol: &SymbolInfo) {
    let location = match symbol.span {
        Some(span) => format!(
            "{}:{}:{}",
            symbol.filepath,
            span.start.lineno + 1,
            span.start.col + 1
        ),
        None => symbol.filepath.to_string(),
    };
    let id_str = format!("{:016x}", symbol.id);

    if let Some(ty) = &symbol.ty {
        println!(
            "  {} {} -> {} @ {} [id={}]",
            symbol.kind.as_str(),
            symbol.name,
            ty,
            location,
            id_str
        );
    } else {
        println!(
            "  {} {} @ {} [id={}]",
            symbol.kind.as_str(),
            symbol.name,
            location,
            id_str
        );
    }

    if let Some(doc) = &symbol.doc {
        for line in doc.lines() {
            println!("    {}", line);
        }
    }
}

fn emit_text_definition(def: &DefinitionInfo) {
    let usage_src = def
        .usage_span
        .as_ref()
        .map(|s| format!(" ({}:{})", def.usage_filepath, s))
        .unwrap_or_else(|| format!(" ({})", def.usage_filepath));

    match &def.definition_path {
        Some(def_path) if def_path != &def.usage_path => {
            println!("  {}{} -> {}", def.usage_path, usage_src, def_path);
        }
        _ => {
            println!("  {}{}", def.usage_path, usage_src);
        }
    }
}

fn source_to_json(src: Source) -> String {
    let path = escape_json(&src.filepath.to_string());
    let span_json = match src.span {
        Some(span) => span_to_json(span),
        None => "null".to_string(),
    };

    format!("{{\"path\":\"{}\",\"span\":{}}}", path, span_json)
}

fn span_to_json(span: Span) -> String {
    let start = pos_to_json(span.start);
    let end = pos_to_json(span.end);
    format!("{{\"start\":{},\"end\":{}}}", start, end)
}

fn pos_to_json(pos: Pos) -> String {
    format!("{{\"line\":{},\"column\":{}}}", pos.lineno + 1, pos.col + 1)
}

fn symbol_to_json(symbol: SymbolInfo) -> String {
    let kind = escape_json(symbol.kind.as_str());
    let name = escape_json(&symbol.name);
    let path = escape_json(&symbol.filepath.to_string());
    let span_json = match symbol.span {
        Some(span) => span_to_json(span),
        None => "null".to_string(),
    };
    let ty_json = match symbol.ty {
        Some(ty) => format!("\"{}\"", escape_json(&ty)),
        None => "null".to_string(),
    };
    let doc_json = match symbol.doc {
        Some(doc) => format!("\"{}\"", escape_json(&doc)),
        None => "null".to_string(),
    };

    format!(
        "{{\"id\":{},\"kind\":\"{}\",\"name\":\"{}\",\"path\":\"{}\",\"span\":{},\"type\":{},\"doc\":{}}}",
        symbol.id, kind, name, path, span_json, ty_json, doc_json
    )
}

fn type_to_json(info: TypeInfo) -> String {
    let ty = escape_json(&info.ty);
    let path = escape_json(&info.filepath.to_string());
    let span_json = match info.span {
        Some(span) => span_to_json(span),
        None => "null".to_string(),
    };

    format!(
        "{{\"id\":{},\"path\":\"{}\",\"span\":{},\"type\":\"{}\",\"is_scheme\":{}}}",
        info.id,
        path,
        span_json,
        ty,
        if info.is_scheme { "true" } else { "false" }
    )
}

fn definition_to_json(def: DefinitionInfo) -> String {
    let usage_path = escape_json(&def.usage_path.to_string());
    let usage_file = escape_json(&def.usage_filepath.to_string());
    let usage_span = match def.usage_span {
        Some(span) => span_to_json(span),
        None => "null".to_string(),
    };
    let definition_id = match def.definition_id {
        Some(id) => id.to_string(),
        None => "null".to_string(),
    };
    let definition_path = def
        .definition_path
        .as_ref()
        .map(|p| format!("\"{}\"", escape_json(&p.to_string())))
        .unwrap_or_else(|| "null".to_string());
    let definition_file = def
        .definition_filepath
        .as_ref()
        .map(|p| format!("\"{}\"", escape_json(&p.to_string())))
        .unwrap_or_else(|| "null".to_string());
    let definition_span = match def.definition_span {
        Some(span) => span_to_json(span),
        None => "null".to_string(),
    };
    let definition_doc = def
        .definition_doc
        .as_ref()
        .map(|doc| format!("\"{}\"", escape_json(doc)))
        .unwrap_or_else(|| "null".to_string());

    format!(
        "{{\"usage\":{{\"id\":{},\"path\":\"{}\",\"file\":\"{}\",\"span\":{}}},\"definition\":{{\"id\":{},\"path\":{},\"file\":{},\"span\":{},\"doc\":{}}}}}",
        def.usage_id,
        usage_path,
        usage_file,
        usage_span,
        definition_id,
        definition_path,
        definition_file,
        definition_span,
        definition_doc
    )
}

// -----------------------------------------------------------------------------
// Collection functions
// -----------------------------------------------------------------------------

pub fn collect_symbols(db: &Database) -> Vec<SymbolInfo> {
    let mut symbols = Vec::new();
    let mut seen = HashSet::new();

    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        let srcmap = &parse_result.source_map;

        for decl in &parse_result.ast.decls {
            let source = srcmap.get(decl);
            let span = source.span;
            let filepath = source.filepath.clone();
            let doc = srcmap.doc(decl).cloned();

            match &decl.value {
                Decl::Func(func) => {
                    let name = func.sig.path.to_string();
                    if !seen.insert(name.clone()) {
                        continue;
                    }
                    let ty = type_info_for_node(db, decl.id).map(|(ty, _)| ty);
                    symbols.push(SymbolInfo {
                        id: decl.id,
                        name,
                        kind: SymbolKind::Function,
                        filepath: filepath.clone(),
                        span,
                        ty,
                        parent_id: None,
                        doc: doc.clone(),
                    });
                }
                Decl::Struct(st) => {
                    let name = st.path.value.to_string();
                    if !seen.insert(name.clone()) {
                        continue;
                    }
                    let struct_id = decl.id;
                    symbols.push(SymbolInfo {
                        id: struct_id,
                        name,
                        kind: SymbolKind::Struct,
                        filepath: filepath.clone(),
                        span,
                        ty: None,
                        parent_id: None,
                        doc: doc.clone(),
                    });

                    if let Some(fields) = &st.fields {
                        for field in fields {
                            let field_name = field.to_string();
                            let field_source = srcmap.get(field);
                            let field_span = field_source.span;
                            let field_doc = srcmap.doc(field).cloned();
                            symbols.push(SymbolInfo {
                                id: field.id,
                                name: field_name,
                                kind: SymbolKind::Field,
                                filepath: field_source.filepath.clone(),
                                span: field_span,
                                ty: type_info_for_node(db, field.id).map(|(ty, _)| ty),
                                parent_id: Some(struct_id),
                                doc: field_doc,
                            });
                        }
                    }
                }
                Decl::Trait(tr) => {
                    let name = tr.ty.to_string();
                    if !seen.insert(name.clone()) {
                        continue;
                    }
                    symbols.push(SymbolInfo {
                        id: decl.id,
                        name,
                        kind: SymbolKind::Trait,
                        filepath: filepath.clone(),
                        span,
                        ty: None,
                        parent_id: None,
                        doc: doc.clone(),
                    });
                }
                Decl::TypeAlias(alias_name, alias_ty) => {
                    let name = alias_name.value.path.to_string();
                    if !seen.insert(name.clone()) {
                        continue;
                    }
                    symbols.push(SymbolInfo {
                        id: decl.id,
                        name,
                        kind: SymbolKind::TypeAlias,
                        filepath: filepath.clone(),
                        span,
                        ty: Some(alias_ty.to_string()),
                        parent_id: None,
                        doc: doc.clone(),
                    });
                }
                _ => {}
            }
        }
    }
    symbols
}

/// Get type information for a node using queries.
///
/// Returns (type_string, is_scheme) where is_scheme indicates if this is a
/// polymorphic type scheme (true) or a monomorphic type (false).
fn type_info_for_node(db: &Database, node_id: NodeId) -> Option<(String, bool)> {
    // For top-level definitions, try to get the polymorphic scheme
    let target = DefTarget::Workspace(node_id.owner);
    if let Some(scheme) = def_scheme(db, target) {
        // Only return the scheme if this node is the "root" of the definition
        // (index 0 typically represents the definition node itself)
        if node_id.index <= 1 {
            return Some((scheme.to_string(), scheme.is_polymorphic()));
        }
    }

    // For expression nodes, get the inferred mono type
    ty_of(db, node_id).map(|ty| (ty.to_string(), false))
}

pub fn collect_types(db: &Database) -> Vec<TypeInfo> {
    let mut types = Vec::new();

    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        let srcmap = &parse_result.source_map;

        for decl in &parse_result.ast.decls {
            if let Some((ty_str, is_scheme)) = type_info_for_node(db, decl.id) {
                let source = srcmap.get(decl);
                types.push(TypeInfo {
                    id: decl.id,
                    filepath: source.filepath.clone(),
                    span: source.span,
                    ty: ty_str,
                    is_scheme,
                });
            }

            if let Decl::Func(func) = &decl.value {
                for param in &func.sig.params {
                    maybe_push_node_type(&mut types, db, srcmap, param);
                }

                if let Some(body) = &func.body {
                    maybe_push_node_type(&mut types, db, srcmap, body);
                }
            }
        }
    }

    types.sort_by(|a, b| {
        a.filepath
            .cmp(&b.filepath)
            .then_with(|| compare_span(a.span, b.span))
            .then_with(|| a.id.cmp(&b.id))
    });

    log::debug!("collected {} type entries", types.len());

    types
}

pub fn collect_definitions(db: &Database) -> Vec<DefinitionInfo> {
    let mut definitions = Vec::new();
    let mut seen_usage_ids = HashSet::new();

    let workspace = db.get_input::<WorkspaceSnapshot>(());
    for file_id in workspace.all_file_ids() {
        let parse_result = parse_file(db, file_id);
        let srcmap = &parse_result.source_map;
        let resolutions = name_resolutions(db, file_id);

        for (usage_id, _resolution) in resolutions.iter() {
            if !seen_usage_ids.insert(*usage_id) {
                continue;
            }

            // Get usage location from source map
            let usage_source = match srcmap.get_by_id(*usage_id) {
                Some(src) => src,
                None => continue,
            };

            // Use symbol_targets to resolve to definition(s)
            let targets = symbol_targets(db, *usage_id);
            if targets.is_empty() {
                continue;
            }

            // Skip definition sites - we only want references
            if targets.iter().any(|t| t.role == SymbolRole::Definition) {
                continue;
            }

            // Get the first target (primary definition)
            let target = &targets[0];
            let SymbolIdentity::Def(def_target) = &target.identity else {
                // Skip local bindings for now - they don't have paths
                continue;
            };

            // Get definition path and location
            let definition_path = def_path(db, def_target.clone());
            let definition_span = match def_target {
                DefTarget::Workspace(def_id) => {
                    let def_node_id = NodeId {
                        owner: *def_id,
                        index: 0,
                    };
                    span_of(db, def_node_id)
                }
                DefTarget::Library(_) | DefTarget::Primitive(_) => None,
            };

            // Get the filepath for the definition
            let definition_filepath = match def_target {
                DefTarget::Workspace(def_id) => workspace
                    .file_info(def_id.file)
                    .map(|info| info.path.clone()),
                DefTarget::Library(_) | DefTarget::Primitive(_) => None,
            };

            // Construct usage path from the definition path
            let usage_path = definition_path
                .clone()
                .unwrap_or_else(|| ItemPath::from(format!("<unknown:{}>", usage_id).as_str()));

            definitions.push(DefinitionInfo {
                usage_id: *usage_id,
                usage_path,
                usage_filepath: usage_source.filepath.clone(),
                usage_span: usage_source.span,
                definition_id: match def_target {
                    DefTarget::Workspace(def_id) => Some(NodeId {
                        owner: *def_id,
                        index: 0,
                    }),
                    _ => None,
                },
                definition_path,
                definition_filepath,
                definition_span,
                definition_doc: None,
            });
        }
    }

    definitions.sort_by(|a, b| {
        a.usage_filepath
            .cmp(&b.usage_filepath)
            .then_with(|| compare_span(a.usage_span, b.usage_span))
            .then_with(|| a.usage_id.cmp(&b.usage_id))
    });

    log::debug!("collected {} definition entries", definitions.len());

    definitions
}

fn compare_span(a: Option<Span>, b: Option<Span>) -> Ordering {
    match (a, b) {
        (Some(a), Some(b)) => (a.start.lineno, a.start.col, a.end.lineno, a.end.col).cmp(&(
            b.start.lineno,
            b.start.col,
            b.end.lineno,
            b.end.col,
        )),
        (Some(_), None) => Ordering::Less,
        (None, Some(_)) => Ordering::Greater,
        (None, None) => Ordering::Equal,
    }
}

fn maybe_push_node_type<T>(
    entries: &mut Vec<TypeInfo>,
    db: &Database,
    srcmap: &SourceMap,
    node: &Node<T>,
) {
    if let Some((ty_str, is_scheme)) = type_info_for_node(db, node.id) {
        let source = srcmap.get(node);
        entries.push(TypeInfo {
            id: node.id,
            filepath: source.filepath.clone(),
            span: source.span,
            ty: ty_str,
            is_scheme,
        });
    }
}
