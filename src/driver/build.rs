use std::str::FromStr;

use crate::pathlib::FilePath;
use crate::target::Target;

use clap::StructOpt;
// use clap::ArgAction::

#[derive(Debug, Default, StructOpt)]
pub struct BuildOptions {
    #[clap(name = "INPUT", help = "entrypoint of the program", action = clap::ArgAction::Set)]
    pub input_path: FilePath,

    #[clap(long = "stdout", help = "Writes output to stdout", action = clap::ArgAction::SetTrue)]
    pub to_stdout: bool,

    #[clap(
        long = "assembly",
        short = 'S',
        help = "Write out assembly instead of compiling",
        action = clap::ArgAction::SetTrue
    )]
    pub write_assembly: bool,

    #[clap(
        long = "optimize",
        short = 'O',
        help = "Set optimize level",
        default_value = "2",
        action = clap::ArgAction::Set
    )]
    pub max_optimize_level: i8,

    #[clap(long, help = "Emit LIR or LLVM IR to output", action = clap::ArgAction::Set)]
    pub emit: Option<EmitType>,

    #[clap(long, help = "Print the AST after parsing", action = clap::ArgAction::SetTrue)]
    pub print_ast: bool,

    #[clap(long = "skip-compile", short = 'K', help = "Skip compilation step", action = clap::ArgAction::SetTrue)]
    pub no_compile: bool,

    #[clap(long, help = "Disable automatic import of `core` library", action = clap::ArgAction::SetTrue)]
    pub no_core: bool,

    #[clap(
        long,
        short,
        help = "Compile target",
        action = clap::ArgAction::Set,
    )]
    pub target: Option<Target>,

    #[clap(long, short, help = "Output path", action = clap::ArgAction::Set)]
    pub output_path: Option<FilePath>,

    #[clap(
        long = "include",
        short = 'I',
        help = "Add directory to C include search path",
        action = clap::ArgAction::Append,
    )]
    pub c_include_paths: Option<Vec<FilePath>>,

    #[clap(long = "link", short = 'L', help = "Link in module", action = clap::ArgAction::Append)]
    pub link_modules: Option<Vec<FilePath>>,

    #[clap(
        long = "lib",
        help = "Build a library (without library)",
        action = clap::ArgAction::SetTrue,
    )]
    pub build_lib: bool,
}

#[derive(Debug, Clone)]
pub enum EmitType {
    LIR,
    LLVMIR,
}

impl BuildOptions {
    pub fn get_target(&self) -> Target {
        // TODO: get the local target
        self.target.unwrap_or_else(Target::default)
    }
}

impl FromStr for EmitType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "lir" => Ok(EmitType::LIR),
            "llvm" | "llvmir" | "llvm-ir" => Ok(EmitType::LLVMIR),
            s => Err(format!("invalid emit type: {}", s)),
        }
    }
}
