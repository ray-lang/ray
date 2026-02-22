use clap::Args;
use ray_shared::optlevel::OptLevel;
use ray_shared::pathlib::FilePath;

use crate::build::EmitType;

/// Options for the `ray test` command.
#[derive(Debug, Default, Args)]
pub struct TestOptions {
    #[arg(value_name = "INPUT", help = "entrypoint of the test file")]
    pub input_path: FilePath,

    #[arg(
        long = "no-core",
        help = "Disable automatic import of `core` library",
        action = clap::ArgAction::SetTrue
    )]
    pub no_core: bool,

    #[arg(value_enum, long, help = "Emit LIR or LLVM IR to output")]
    pub emit: Option<EmitType>,

    #[arg(
        long = "optimize",
        short = 'O',
        help = "Set optimize level",
        default_value = "2",
        action = clap::ArgAction::Set
    )]
    pub opt_level: OptLevel,
}
