use clap::Args;
use ray_core::pathlib::FilePath;

#[derive(Debug, Args)]
pub struct GlobalOptions {
    #[arg(
        value_name = "root-path",
        long = "root-path",
        env = "RAY_PATH",
        help = "Root path for ray libraries and sources",
        long_help = "If not provided, it will default to `$HOME/.ray`. If that path is inaccessible, then /opt/ray will be used.",
        global = true
    )]
    pub root_path: Option<FilePath>,

    #[arg(
        long,
        env = "LOG_LEVEL",
        help = "Sets the log level",
        default_value = "info",
        hide = true,
        global = true
    )]
    pub log_level: log::LevelFilter,

    #[arg(
        long,
        help = "Runs in profiling mode, outputting to profile-<DATE>.pb",
        hide = true,
        global = true
    )]
    pub profile: bool,
}
