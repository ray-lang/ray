use std::{fs, io};

use clap::Args;
use ray_codegen::libgen::RayLib;
use ray_frontend::queries::{
    display::{build_rename_subst, format_func_display, format_impl_sig},
    libraries::{LibraryData, OperatorArity},
};
use ray_shared::{
    def::LibraryDefId,
    pathlib::FilePath,
    resolution::DefTarget,
    ty::{Ty, TyVar},
};
use ray_typing::types::{Substitutable, TyScheme};
use serde::Serialize;

/// Options for the `inspect` subcommand.
#[derive(Debug, Args)]
pub struct InspectOptions {
    #[arg(value_name = "FILE", help = "Path to a .raylib file")]
    pub input_path: FilePath,

    #[arg(long = "json", help = "Output as JSON", default_value = "false")]
    pub json: bool,

    #[arg(long = "functions", help = "Show exported functions")]
    pub functions: bool,

    #[arg(long = "structs", help = "Show struct definitions")]
    pub structs: bool,

    #[arg(long = "traits", help = "Show trait definitions")]
    pub traits: bool,

    #[arg(long = "impls", help = "Show impl blocks")]
    pub impls: bool,

    #[arg(long = "operators", help = "Show operator registrations")]
    pub operators: bool,

    #[arg(long = "lir", help = "Dump the full LIR program")]
    pub lir: bool,

    #[arg(long = "lir-funcs", help = "List LIR function signatures")]
    pub lir_funcs: bool,

    #[arg(long = "all", help = "Show all sections")]
    pub all: bool,
}

impl InspectOptions {
    fn show_functions(&self) -> bool {
        self.all || self.functions
    }

    fn show_structs(&self) -> bool {
        self.all || self.structs
    }

    fn show_traits(&self) -> bool {
        self.all || self.traits
    }

    fn show_impls(&self) -> bool {
        self.all || self.impls
    }

    fn show_operators(&self) -> bool {
        self.all || self.operators
    }

    fn show_lir(&self) -> bool {
        self.all || self.lir
    }

    fn show_lir_funcs(&self) -> bool {
        self.all || self.lir_funcs
    }
}

// ============================================================================
// Report types
// ============================================================================

#[derive(Debug, Serialize)]
pub struct InspectSummary {
    pub functions: usize,
    pub structs: usize,
    pub traits: usize,
    pub impls: usize,
    pub operators: usize,
}

#[derive(Debug, Serialize)]
pub struct FunctionEntry {
    pub path: String,
    pub signature: String,
}

#[derive(Debug, Serialize)]
pub struct StructEntry {
    pub path: String,
    pub scheme: String,
    pub fields: Vec<StructFieldEntry>,
}

#[derive(Debug, Serialize)]
pub struct StructFieldEntry {
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Serialize)]
pub struct MethodEntry {
    pub name: String,
    pub signature: String,
}

#[derive(Debug, Serialize)]
pub struct TraitEntry {
    pub path: String,
    pub ty: String,
    pub methods: Vec<MethodEntry>,
}

#[derive(Debug, Serialize)]
pub struct ImplEntry {
    pub signature: String,
    pub methods: Vec<MethodEntry>,
}

#[derive(Debug, Serialize)]
pub struct OperatorEntryInfo {
    pub symbol: String,
    pub arity: String,
    pub trait_def: String,
}

#[derive(Debug, Serialize)]
pub struct LirFuncEntry {
    pub name: String,
    pub signature: String,
}

#[derive(Debug, Serialize)]
pub struct InspectReport {
    pub file_path: String,
    pub file_size: u64,
    pub modules: Vec<String>,
    pub summary: InspectSummary,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub functions: Option<Vec<FunctionEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub structs: Option<Vec<StructEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub traits: Option<Vec<TraitEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub impls: Option<Vec<ImplEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operators: Option<Vec<OperatorEntryInfo>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lir: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lir_funcs: Option<Vec<LirFuncEntry>>,
}

impl InspectReport {
    pub fn emit(self, json: bool) {
        if json {
            self.emit_json();
        } else {
            self.emit_text();
        }
    }

    fn emit_text(self) {
        println!(
            "Library: {} ({})",
            self.file_path,
            format_size(self.file_size)
        );
        println!();

        if !self.modules.is_empty() {
            println!("Modules:");
            for module in &self.modules {
                println!("  {}", module);
            }
            println!();
        }

        println!("Summary:");
        println!("  Functions:  {}", self.summary.functions);
        println!("  Structs:    {}", self.summary.structs);
        println!("  Traits:     {}", self.summary.traits);
        println!("  Impls:      {}", self.summary.impls);
        println!("  Operators:  {}", self.summary.operators);

        if let Some(functions) = &self.functions {
            println!();
            println!("Functions ({}):", functions.len());
            for f in functions {
                println!("  {}", f.signature);
            }
        }

        if let Some(structs) = &self.structs {
            println!();
            println!("Structs ({}):", structs.len());
            for s in structs {
                println!("  struct {} :: {}", s.path, s.scheme);
                for field in &s.fields {
                    println!("    {}: {}", field.name, field.ty);
                }
            }
        }

        if let Some(traits) = &self.traits {
            println!();
            println!("Traits ({}):", traits.len());
            for t in traits {
                println!("  trait {}", t.ty);
                for method in &t.methods {
                    println!("    {}", method.signature);
                }
            }
        }

        if let Some(impls) = &self.impls {
            println!();
            println!("Impls ({}):", impls.len());
            for imp in impls {
                println!("  {}", imp.signature);
                for method in &imp.methods {
                    println!("    {}", method.signature);
                }
            }
        }

        if let Some(operators) = &self.operators {
            println!();
            println!("Operators ({}):", operators.len());
            for op in operators {
                println!("  {} ({}) -> {}", op.symbol, op.arity, op.trait_def);
            }
        }

        if let Some(lir_funcs) = &self.lir_funcs {
            println!();
            println!("LIR Functions ({}):", lir_funcs.len());
            for f in lir_funcs {
                println!("  {}", f.signature);
            }
        }

        if let Some(lir) = &self.lir {
            println!();
            println!("LIR Program:");
            println!("{}", lir);
        }
    }

    fn emit_json(self) {
        println!("{}", serde_json::to_string_pretty(&self).unwrap());
    }
}

// ============================================================================
// Main inspect function
// ============================================================================

/// Inspect a precompiled .raylib file and return a report.
pub fn inspect(options: &InspectOptions) -> Result<InspectReport, io::Error> {
    let path = &options.input_path;
    let metadata = fs::metadata(path.as_ref())?;
    let file_size = metadata.len();

    let file = fs::File::open(path.as_ref())?;
    let raylib: RayLib = bincode::deserialize_from(&file)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

    let data = &raylib.data;
    let program = &raylib.program;

    let modules = {
        let mut mods: Vec<String> = data.modules.iter().map(|m| m.to_string()).collect();
        mods.sort();
        mods
    };

    let summary = build_summary(data);

    let functions = if options.show_functions() {
        Some(collect_functions(data))
    } else {
        None
    };

    let structs = if options.show_structs() {
        Some(collect_structs(data))
    } else {
        None
    };

    let traits = if options.show_traits() {
        Some(collect_traits(data))
    } else {
        None
    };

    let impls = if options.show_impls() {
        Some(collect_impls(data))
    } else {
        None
    };

    let operators = if options.show_operators() {
        Some(collect_operators(data))
    } else {
        None
    };

    let lir = if options.show_lir() {
        Some(format!("{}", program))
    } else {
        None
    };

    let lir_funcs = if options.show_lir_funcs() {
        Some(collect_lir_funcs(program))
    } else {
        None
    };

    Ok(InspectReport {
        file_path: path.to_string(),
        file_size,
        modules,
        summary,
        functions,
        structs,
        traits,
        impls,
        operators,
        lir,
        lir_funcs,
    })
}

// ============================================================================
// Formatting helpers
// ============================================================================

fn format_size(bytes: u64) -> String {
    if bytes >= 1_048_576 {
        format!("{:.1} MB", bytes as f64 / 1_048_576.0)
    } else if bytes >= 1024 {
        format!("{:.1} KB", bytes as f64 / 1024.0)
    } else {
        format!("{} B", bytes)
    }
}

// ============================================================================
// Display variable mapping (schema vars → user vars)
// ============================================================================

/// Apply display variable mapping to a TyScheme, returning a display-friendly copy.
fn display_scheme(data: &LibraryData, lib_id: &LibraryDefId, scheme: &TyScheme) -> TyScheme {
    if let Some(reverse_map) = data.display_vars.get(lib_id) {
        if !reverse_map.is_empty() {
            let subst = build_rename_subst(reverse_map);
            let mut result = scheme.clone();
            result.apply_subst(&subst);
            return result;
        }
    }
    scheme.clone()
}

/// Apply display variable mapping to a Ty, returning a display-friendly copy.
fn display_ty(data: &LibraryData, lib_id: &LibraryDefId, ty: &Ty) -> Ty {
    if let Some(reverse_map) = data.display_vars.get(lib_id) {
        if !reverse_map.is_empty() {
            let subst = build_rename_subst(reverse_map);
            let mut result = ty.clone();
            result.apply_subst(&subst);
            return result;
        }
    }
    ty.clone()
}

/// Apply display variable mapping to TyVars, returning display-friendly copies.
fn display_vars(data: &LibraryData, lib_id: &LibraryDefId, vars: &[TyVar]) -> Vec<TyVar> {
    if let Some(reverse_map) = data.display_vars.get(lib_id) {
        if !reverse_map.is_empty() {
            return vars
                .iter()
                .map(|v| reverse_map.get(v).cloned().unwrap_or_else(|| v.clone()))
                .collect();
        }
    }
    vars.to_vec()
}

// ============================================================================
// Collection functions
// ============================================================================

fn build_summary(data: &LibraryData) -> InspectSummary {
    InspectSummary {
        functions: data.func_defs.len(),
        structs: data.structs.len(),
        traits: data.traits.len(),
        impls: data.impls.len(),
        operators: data.operators.len(),
    }
}

fn collect_functions(data: &LibraryData) -> Vec<FunctionEntry> {
    let mut entries: Vec<FunctionEntry> = data
        .func_defs
        .iter()
        .map(|(lib_id, fdef)| {
            let path = data
                .paths
                .get(lib_id)
                .map(|p| p.to_string())
                .unwrap_or_else(|| fdef.path.to_string());
            let scheme = display_scheme(data, lib_id, &fdef.scheme);
            let name = fdef
                .path
                .item_name()
                .unwrap_or_else(|| path.as_str())
                .to_string();
            let param_names: Vec<String> = fdef.params.iter().map(|p| p.name.clone()).collect();
            let signature =
                format_func_display(&path, &scheme, &param_names, &fdef.modifiers, None);
            FunctionEntry {
                path: name,
                signature,
            }
        })
        .collect();
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    entries
}

fn collect_structs(data: &LibraryData) -> Vec<StructEntry> {
    let mut entries: Vec<StructEntry> = data
        .structs
        .iter()
        .map(|(lib_id, sdef)| {
            let scheme = display_scheme(data, lib_id, &sdef.ty);
            StructEntry {
                path: sdef.path.to_string(),
                scheme: scheme.to_string(),
                fields: sdef
                    .fields
                    .iter()
                    .map(|f| {
                        let field_ty = display_scheme(data, lib_id, &f.ty);
                        StructFieldEntry {
                            name: f.name.clone(),
                            ty: field_ty.to_string(),
                        }
                    })
                    .collect(),
            }
        })
        .collect();
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    entries
}

fn collect_traits(data: &LibraryData) -> Vec<TraitEntry> {
    let mut entries: Vec<TraitEntry> = data
        .traits
        .iter()
        .map(|(lib_id, tdef)| {
            let ty = display_ty(data, lib_id, &tdef.ty);
            let parent_vars = display_vars(data, lib_id, &tdef.type_params);
            let parent_display = (parent_vars, vec![]);
            let methods = tdef
                .methods
                .iter()
                .map(|m| {
                    let method_lib_id = lib_id_from_target(&m.target);
                    let scheme = match method_lib_id {
                        Some(id) => display_scheme(data, id, &m.scheme),
                        None => m.scheme.clone(),
                    };
                    MethodEntry {
                        name: m.name.clone(),
                        signature: format_func_display(
                            &m.name,
                            &scheme,
                            &[],
                            &[],
                            Some(&parent_display),
                        ),
                    }
                })
                .collect();
            TraitEntry {
                path: tdef.path.to_string(),
                ty: ty.to_string(),
                methods,
            }
        })
        .collect();
    entries.sort_by(|a, b| a.path.cmp(&b.path));
    entries
}

fn collect_impls(data: &LibraryData) -> Vec<ImplEntry> {
    let mut entries: Vec<ImplEntry> = data
        .impls
        .iter()
        .map(|(lib_id, idef)| {
            let type_params = display_vars(data, lib_id, &idef.type_params);
            let display_impl_ty = display_ty(data, lib_id, &idef.implementing_type);
            let display_trait = idef.trait_ty.as_ref().map(|t| display_ty(data, lib_id, t));
            let display_preds: Vec<_> = idef
                .predicates
                .iter()
                .map(|p| {
                    let subst = data
                        .display_vars
                        .get(lib_id)
                        .filter(|m| !m.is_empty())
                        .map(build_rename_subst);
                    match subst {
                        Some(s) => {
                            let mut p = p.clone();
                            p.apply_subst(&s);
                            p
                        }
                        None => p.clone(),
                    }
                })
                .collect();

            let signature =
                format_impl_sig(&display_impl_ty, display_trait.as_ref(), &display_preds);

            let parent_display = (type_params, display_preds);
            let methods = idef
                .methods
                .iter()
                .map(|m| {
                    let method_lib_id = lib_id_from_target(&m.target);
                    let scheme = match method_lib_id {
                        Some(id) => display_scheme(data, id, &m.scheme),
                        None => m.scheme.clone(),
                    };
                    MethodEntry {
                        name: m.name.clone(),
                        signature: format_func_display(
                            &m.name,
                            &scheme,
                            &[],
                            &[],
                            Some(&parent_display),
                        ),
                    }
                })
                .collect();

            ImplEntry { signature, methods }
        })
        .collect();
    entries.sort_by(|a, b| a.signature.cmp(&b.signature));
    entries
}

fn collect_operators(data: &LibraryData) -> Vec<OperatorEntryInfo> {
    let mut entries: Vec<OperatorEntryInfo> = data
        .operators
        .iter()
        .map(|((sym, arity), entry)| {
            let arity_str = match arity {
                OperatorArity::Prefix => "prefix",
                OperatorArity::Infix => "infix",
            };
            OperatorEntryInfo {
                symbol: sym.clone(),
                arity: arity_str.to_string(),
                trait_def: format!("{:?}", entry.trait_def),
            }
        })
        .collect();
    entries.sort_by(|a, b| a.symbol.cmp(&b.symbol));
    entries
}

fn collect_lir_funcs(program: &ray_lir::Program) -> Vec<LirFuncEntry> {
    let mut entries: Vec<LirFuncEntry> = program
        .funcs
        .iter()
        .map(|func| LirFuncEntry {
            name: func.name.to_string(),
            signature: func.format_signature(),
        })
        .collect();
    entries.sort_by(|a, b| a.name.cmp(&b.name));
    entries
}

/// Get the LibraryDefId from a DefTarget, if it's a library def.
fn lib_id_from_target(target: &DefTarget) -> Option<&LibraryDefId> {
    match target {
        DefTarget::Library(id) => Some(id),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::io::Write;

    use ray_codegen::libgen;
    use ray_frontend::queries::{
        defs::{FuncDef, ImplDef, MethodInfo, ParamDef, StructDef, StructField, TraitDef},
        libraries::LibraryData,
    };
    use ray_shared::{
        def::LibraryDefId,
        pathlib::{ItemPath, ModulePath},
        resolution::DefTarget,
        ty::{Ty, TyVar},
    };
    use ray_typing::types::{ReceiverMode, TyScheme};
    use tempfile::NamedTempFile;

    use super::{InspectOptions, inspect};

    fn make_options(path: &std::path::Path) -> InspectOptions {
        InspectOptions {
            input_path: path.into(),
            json: false,
            functions: false,
            structs: false,
            traits: false,
            impls: false,
            operators: false,
            lir: false,
            lir_funcs: false,
            all: false,
        }
    }

    fn write_raylib(data: LibraryData) -> NamedTempFile {
        let program = ray_lir::Program::new("test");
        let bytes = libgen::serialize(data, program);
        let mut tmp = NamedTempFile::new().unwrap();
        tmp.write_all(&bytes).unwrap();
        tmp
    }

    #[test]
    fn test_inspect_report_from_empty_library() {
        let tmp = write_raylib(LibraryData::default());
        let options = make_options(tmp.path());
        let report = inspect(&options).unwrap();

        assert_eq!(report.summary.functions, 0);
        assert_eq!(report.summary.structs, 0);
        assert_eq!(report.summary.traits, 0);
        assert_eq!(report.summary.impls, 0);
        assert_eq!(report.summary.operators, 0);
        assert!(report.modules.is_empty());
    }

    #[test]
    fn test_inspect_report_counts() {
        let mut data = LibraryData::default();

        let lib_id = |idx: u32| LibraryDefId {
            module: ModulePath::from("test"),
            index: idx,
        };

        // Add a struct
        data.structs.insert(
            lib_id(0),
            StructDef {
                target: DefTarget::Library(lib_id(0)),
                path: ItemPath::from("test::Foo"),
                ty: TyScheme::from_mono(Ty::unit()),
                fields: vec![StructField {
                    name: "x".to_string(),
                    ty: TyScheme::from_mono(Ty::int()),
                }],
            },
        );

        // Add a trait
        data.traits.insert(
            lib_id(1),
            TraitDef {
                target: DefTarget::Library(lib_id(1)),
                path: ItemPath::from("test::Bar"),
                ty: Ty::Proj(ItemPath::from("test::Bar"), vec![Ty::Var(TyVar::new("'a"))]),
                type_params: vec![TyVar::new("'a")],
                super_traits: vec![],
                methods: vec![],
                default_ty: None,
            },
        );

        // Add an impl
        data.impls.insert(
            lib_id(2),
            ImplDef {
                target: DefTarget::Library(lib_id(2)),
                type_params: vec![],
                implementing_type: Ty::int(),
                trait_ty: None,
                predicates: vec![],
                methods: vec![MethodInfo {
                    target: DefTarget::Library(lib_id(3)),
                    path: ItemPath::from("test::int::to_string"),
                    name: "to_string".to_string(),
                    is_static: false,
                    recv_mode: ReceiverMode::Value,
                    scheme: TyScheme::from_mono(Ty::string()),
                }],
            },
        );

        // Add a function
        data.func_defs.insert(
            lib_id(4),
            FuncDef {
                target: DefTarget::Library(lib_id(4)),
                path: ItemPath::from("test::greet"),
                scheme: TyScheme::from_mono(Ty::unit()),
                params: vec![ParamDef {
                    name: "name".to_string(),
                    is_move: false,
                }],
                modifiers: vec![],
            },
        );

        let tmp = write_raylib(data);
        let options = make_options(tmp.path());
        let report = inspect(&options).unwrap();

        assert_eq!(report.summary.structs, 1);
        assert_eq!(report.summary.traits, 1);
        assert_eq!(report.summary.impls, 1);
        assert_eq!(report.summary.functions, 1);
    }

    #[test]
    fn test_inspect_report_modules() {
        let mut data = LibraryData::default();
        data.modules = vec![
            ModulePath::from("core"),
            ModulePath::from("core::io"),
            ModulePath::from("core::ops"),
        ];

        let tmp = write_raylib(data);
        let options = make_options(tmp.path());
        let report = inspect(&options).unwrap();

        assert_eq!(report.modules.len(), 3);
        assert!(report.modules.contains(&"core".to_string()));
        assert!(report.modules.contains(&"core::io".to_string()));
        assert!(report.modules.contains(&"core::ops".to_string()));
    }

    #[test]
    fn test_inspect_report_json_roundtrip() {
        let tmp = write_raylib(LibraryData::default());
        let options = make_options(tmp.path());
        let report = inspect(&options).unwrap();

        let json = serde_json::to_string(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed["summary"]["functions"], 0);
        assert_eq!(parsed["summary"]["structs"], 0);
    }

    #[test]
    fn test_inspect_nonexistent_file() {
        let options = InspectOptions {
            input_path: "/nonexistent/path.raylib".into(),
            json: false,
            functions: false,
            structs: false,
            traits: false,
            impls: false,
            operators: false,
            lir: false,
            lir_funcs: false,
            all: false,
        };
        let result = inspect(&options);
        assert!(result.is_err());
    }

    #[test]
    fn test_display_vars_applied_to_functions() {
        let mut data = LibraryData::default();
        let lib_id = LibraryDefId {
            module: ModulePath::from("test"),
            index: 0,
        };

        let schema_var = TyVar::new("?s0");
        let user_var = TyVar::new("'a");

        data.func_defs.insert(
            lib_id.clone(),
            FuncDef {
                target: DefTarget::Library(lib_id.clone()),
                path: ItemPath::from("test::identity"),
                scheme: TyScheme::new(
                    vec![schema_var.clone()],
                    vec![],
                    Ty::Func(
                        vec![Ty::Var(schema_var.clone())],
                        Box::new(Ty::Var(schema_var.clone())),
                    ),
                ),
                params: vec![ParamDef {
                    name: "x".to_string(),
                    is_move: false,
                }],
                modifiers: vec![],
            },
        );

        let mut reverse_map = HashMap::new();
        reverse_map.insert(schema_var, user_var);
        data.display_vars.insert(lib_id, reverse_map);

        let tmp = write_raylib(data);
        let mut options = make_options(tmp.path());
        options.functions = true;
        let report = inspect(&options).unwrap();

        let functions = report.functions.unwrap();
        assert_eq!(functions.len(), 1);
        let sig = &functions[0].signature;
        assert!(
            sig.contains("'a"),
            "signature should use display var 'a: {}",
            sig
        );
        assert!(
            !sig.contains("?s0"),
            "signature should not contain schema var ?s0: {}",
            sig
        );
    }
}
