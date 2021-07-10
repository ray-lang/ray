use crate::pathlib::FilePath;
use crate::target::Target;

use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct BuildOptions {
    #[structopt(name = "INPUT", help = "entrypoint of the program")]
    pub input_path: FilePath,

    #[structopt(long = "stdout", help = "Writes output to stdout")]
    pub to_stdout: bool,

    #[structopt(
        long = "assembly",
        short = "S",
        help = "Write out assembly instead of compiling"
    )]
    pub write_assembly: bool,

    #[structopt(
        long = "optimize",
        short = "O",
        help = "Set optimize level",
        default_value = "2"
    )]
    pub max_optimize_level: i8,

    #[structopt(long, help = "Emit IR to output")]
    pub emit_ir: bool,

    #[structopt(long, help = "Print the AST after parsing")]
    pub print_ast: bool,

    #[structopt(long = "skip-compile", short = "K", help = "Skip compilation step")]
    pub no_compile: bool,

    #[structopt(long, help = "Disable automatic import of `core` library")]
    pub no_core: bool,

    #[structopt(
        long,
        short,
        help = "Compile target",
        possible_values = &[
            Target::Wasm32.as_str(),
            Target::Wasm.as_str(),
        ]
    )]
    pub target: Option<Target>,

    #[structopt(long, short, help = "Output path")]
    pub output_path: Option<FilePath>,

    #[structopt(
        long = "include",
        short = "I",
        help = "Add directory to C include search path"
    )]
    pub c_include_paths: Option<Vec<FilePath>>,

    #[structopt(long = "link", short = "L", help = "Link in module")]
    pub link_modules: Option<Vec<FilePath>>,

    #[structopt(long = "lib", help = "Build a library (without library)")]
    pub build_lib: bool,
}

impl BuildOptions {
    pub fn get_target(&self) -> Target {
        // TODO: get the local target
        self.target.unwrap_or_else(|| Target::Wasm32)
    }
}
