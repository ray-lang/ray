use clap::Args;
use ray_shared::pathlib::FilePath;

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
}
