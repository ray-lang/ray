use std::str::FromStr;

use clap::StructOpt;

use crate::{
    ast::Path,
    errors::RayError,
    pathlib::FilePath,
    span::{Pos, Source, Span},
};

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

#[derive(Debug, StructOpt)]
pub struct AnalyzeOptions {
    #[clap(
        name = "INPUT",
        help = "Ray source file to analyze",
        action = clap::ArgAction::Set
    )]
    pub input_path: FilePath,

    #[clap(
        long = "format",
        default_value = "text",
        value_parser = parse_analysis_format,
        action = clap::ArgAction::Set,
        help = "Output format (text or json)"
    )]
    pub format: AnalysisFormat,

    #[clap(
        long = "no-core",
        default_value = "false",
        help = "Disable automatic import of `core` library",
        action = clap::ArgAction::SetTrue
    )]
    pub no_core: bool,
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
    pub id: u64,
    pub name: String,
    pub kind: SymbolKind,
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub ty: Option<String>,
    pub parent_id: Option<u64>,
    pub doc: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub id: u64,
    pub filepath: FilePath,
    pub span: Option<Span>,
    pub ty: String,
    pub is_scheme: bool,
}

#[derive(Debug, Clone)]
pub struct DefinitionInfo {
    pub usage_id: u64,
    pub usage_path: Path,
    pub usage_filepath: FilePath,
    pub usage_span: Option<Span>,
    pub definition_id: Option<u64>,
    pub definition_path: Option<Path>,
    pub definition_filepath: Option<FilePath>,
    pub definition_span: Option<Span>,
    pub definition_doc: Option<String>,
}

#[derive(Debug)]
pub struct AnalysisReport {
    pub format: AnalysisFormat,
    pub input_path: FilePath,
    pub diagnostics: Vec<RayError>,
    pub symbols: Vec<SymbolInfo>,
    pub types: Vec<TypeInfo>,
    pub definitions: Vec<DefinitionInfo>,
}

impl AnalysisReport {
    pub fn new(
        format: AnalysisFormat,
        input_path: FilePath,
        diagnostics: Vec<RayError>,
        symbols: Vec<SymbolInfo>,
        types: Vec<TypeInfo>,
        definitions: Vec<DefinitionInfo>,
    ) -> Self {
        Self {
            format,
            input_path,
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
        }
    }

    fn emit_json(self) {
        let status = self.status();
        let AnalysisReport {
            format: _,
            input_path,
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
            "{{\"status\":\"{}\",\"input\":\"{}\",\"diagnostics\":[{}],\"symbols\":[{}],\"types\":[{}],\"definitions\":[{}]}}",
            status.as_str(),
            escape_json(&input_path.to_string()),
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
