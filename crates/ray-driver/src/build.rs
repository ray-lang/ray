use std::{ffi::OsString, str::FromStr};

use clap::{Args, ValueEnum};
use ray_core::{pathlib::FilePath, target::Target};
use ray_shared::optlevel::OptLevel;

use crate::GlobalOptions;

#[derive(Debug, Default, Args)]
pub struct BuildOptions {
    #[arg(value_name = "INPUT", help = "entrypoint of the program")]
    pub input_path: FilePath,

    #[arg(long = "stdout", help = "Writes output to stdout", action = clap::ArgAction::SetTrue)]
    pub to_stdout: bool,

    #[arg(
        long = "assembly",
        short = 'S',
        help = "Write out assembly instead of compiling",
        action = clap::ArgAction::SetTrue
    )]
    pub write_assembly: bool,

    #[arg(
        long = "optimize",
        short = 'O',
        help = "Set optimize level",
        default_value = "2",
        action = clap::ArgAction::Set
    )]
    pub opt_level: OptLevel,

    #[arg(value_enum, long, help = "Emit LIR or LLVM IR to output")]
    pub emit: Option<EmitType>,

    #[arg(long, help = "Print the AST after parsing", action = clap::ArgAction::SetTrue)]
    pub print_ast: bool,

    #[arg(long = "skip-compile", short = 'K', help = "Skip compilation step", action = clap::ArgAction::SetTrue)]
    pub no_compile: bool,

    #[arg(long, help = "Disable automatic import of `core` library", action = clap::ArgAction::SetTrue)]
    pub no_core: bool,

    #[arg(long, short, help = "Compile target")]
    pub target: Option<Target>,

    #[arg(long, short, help = "Output path")]
    pub output_path: Option<FilePath>,

    #[arg(
        long = "include",
        short = 'I',
        help = "Add directory to C include search path",
        action = clap::ArgAction::Append,
    )]
    pub c_include_paths: Option<Vec<FilePath>>,

    #[arg(long = "link", short = 'L', help = "Link in module", action = clap::ArgAction::Append)]
    pub link_modules: Option<Vec<FilePath>>,

    #[arg(
        long = "lib",
        help = "Build a library (without library)",
        action = clap::ArgAction::SetTrue,
    )]
    pub build_lib: bool,
}

#[derive(Debug, Clone, ValueEnum)]
pub enum EmitType {
    LIR,
    LLVM,
}

impl std::fmt::Display for EmitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitType::LIR => write!(f, "lir"),
            EmitType::LLVM => write!(f, "llvm"),
        }
    }
}

impl BuildOptions {
    pub fn get_target(&self) -> Target {
        // TODO: get the local target
        self.target.unwrap_or_else(Target::default)
    }

    pub fn to_argv(self, globals: GlobalOptions) -> Vec<OsString> {
        let mut args = vec![];

        if let Some(root_path) = globals.root_path {
            args.push("--root-path".into());
            args.push(root_path.to_string().into());
        }

        args.push("--log-level".into());
        args.push(globals.log_level.to_string().to_lowercase().into());

        if self.to_stdout {
            args.push("--stdout".into());
        }

        if self.write_assembly {
            args.push("-S".into());
        }

        args.push("--optimize".into());
        args.push(self.opt_level.to_string().into());

        if let Some(emit) = self.emit {
            args.push("--emit".into());
            args.push(emit.to_string().into());
        }

        if self.print_ast {
            args.push("--print-ast".into());
        }

        if self.no_compile {
            args.push("--no-compile".into());
        }

        if self.no_core {
            args.push("--no-core".into());
        }

        if let Some(target) = self.target {
            args.push("--target".into());
            args.push(target.to_string().into());
        }

        if let Some(output_path) = self.output_path {
            args.push("--output-path".into());
            args.push(output_path.to_string().into());
        }

        if let Some(c_include_paths) = self.c_include_paths {
            for path in c_include_paths {
                args.push(format!("-I{}", path).into());
            }
        }

        if let Some(link_modules) = self.link_modules {
            for path in link_modules {
                args.push(format!("-L{}", path).into());
            }
        }

        if self.build_lib {
            args.push("--lib".into());
        }

        args.push(self.input_path.to_string().into());

        args
    }
}

impl FromStr for EmitType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "lir" => Ok(EmitType::LIR),
            "llvm" | "llvmir" | "llvm-ir" => Ok(EmitType::LLVM),
            s => Err(format!("invalid emit type: {}", s)),
        }
    }
}
