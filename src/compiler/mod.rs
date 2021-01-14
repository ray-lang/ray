use crate::{ast::Module, pathlib::FilePath, target::Target};

#[derive(Debug)]
pub struct CompilerOptions {
    pub input_path: FilePath,
    pub output_path: FilePath,
    pub stdlib_path: FilePath,
    pub target: Target,
    pub build_lib: bool,
    pub write_assembly: bool,
    pub emit_ir: bool,
    pub to_stdout: bool,
    pub no_polymorphism: bool,
    pub synthetic_module: bool,
    pub max_optimize_level: i8,
    pub link_module_paths: Vec<String>,
}

#[derive(Debug)]
pub struct Compiler {}

impl Compiler {
    /// Entry point for the compiler
    pub fn run(options: &CompilerOptions) {
        unimplemented!()
    }

    pub fn compile(&self, m: &Module) {
        unimplemented!()
    }
}
