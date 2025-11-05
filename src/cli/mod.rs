use std::{
    error::Error,
    fs::File,
    io::{self, Write},
    process,
};

use clap::StructOpt;
use colored::{Color, ColoredString, Colorize};
use log::Level;
use pprof::protos::Message;
use ray_core::pathlib::{FilePath, RayPaths};
use ray_driver::{AnalyzeOptions, BuildOptions, Driver};

mod analyze;
mod build;
mod lsp;

#[derive(Debug, StructOpt)]
pub struct Cli {
    #[structopt(flatten)]
    global_options: GlobalOptions,

    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(Debug, StructOpt)]
pub struct GlobalOptions {
    #[clap(
        name = "root-path",
        long = "root-path",
        takes_value = true,
        env = "RAY_PATH",
        help = "root path for ray libraries and sources",
        long_help = "If not provided, it will default to `$HOME/.ray`. If that path is inaccessible, then /opt/ray will be used.",
        global = true,
        action = clap::ArgAction::Set,
    )]
    ray_path: Option<FilePath>,

    #[clap(
        long, env = "LOG_LEVEL",
        help = "Sets the log level",
        default_value = "info",
        hide = true,
        global = true,
        action = clap::ArgAction::Set,
    )]
    log_level: log::LevelFilter,

    #[structopt(
        long,
        help = "Runs in profiling mode, outputting to profile-<DATE>.pb",
        global = true,
        action = clap::ArgAction::SetTrue,
    )]
    profile: bool,
}

#[derive(Debug, StructOpt)]
pub enum Command {
    Build(BuildOptions),
    Analyze(AnalyzeOptions),
    Lsp(lsp::LspOptions),
}

pub struct CmdError {
    msg: String,
}

impl<E: Error> From<E> for CmdError {
    fn from(e: E) -> Self {
        CmdError { msg: e.to_string() }
    }
}

impl Command {
    fn configure_logger(&self) -> Option<fern::Dispatch> {
        match self {
            Command::Build(_) | Command::Analyze(_) => { /* ignore */ }
            Command::Lsp(options) => {
                if let Some(log_file) = &options.log_file {
                    return Some(
                        fern::Dispatch::new()
                            .format(move |out, message, record| {
                                let level = record.level();
                                out.finish(format_args!(
                                    "{}: {}",
                                    level.to_string().to_lowercase(),
                                    message,
                                ))
                            })
                            .chain(fern::log_file(log_file).unwrap()),
                    );
                }
            }
        }

        None
    }
}

pub fn run() {
    // get the subcommand
    let cli = Cli::parse();

    // set up logging
    let mut dispatch = fern::Dispatch::new().level(cli.global_options.log_level);

    if let Some(sub_logger) = cli.cmd.configure_logger() {
        dispatch = dispatch.chain(sub_logger)
    } else {
        dispatch = dispatch
            .format(move |out, message, record| {
                let level = record.level();
                let color = match level {
                    Level::Error => Color::Red,
                    Level::Warn => Color::Yellow,
                    Level::Info => Color::Blue,
                    Level::Debug => Color::Magenta,
                    Level::Trace => Color::Green,
                };
                out.finish(format_args!(
                    "{} {}",
                    ColoredString::from((level.to_string().to_lowercase() + ":").as_str())
                        .color(color)
                        .to_string(),
                    message
                ))
            })
            .chain(io::stderr())
    }

    dispatch.apply().unwrap();

    // get the ray_path
    let explicit_root = cli.global_options.ray_path.clone();
    let ray_paths = if let Some(paths) = RayPaths::discover(explicit_root.clone(), None) {
        paths
    } else if let Some(path) = explicit_root {
        RayPaths::new(path)
    } else {
        eprintln!(
            "error: unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
        );
        process::exit(1);
    };

    let prof = if cli.global_options.profile {
        Some(pprof::ProfilerGuard::new(100).unwrap())
    } else {
        None
    };

    let mut driver = Driver::new(ray_paths);
    match cli.cmd {
        Command::Build(options) => build::action(&mut driver, options),
        Command::Analyze(options) => analyze::action(&mut driver, options),
        Command::Lsp(options) => lsp::action(&mut driver, options),
    }

    if let Some(prof) = prof {
        if let Some(err) = prof
            .report()
            .build()
            .map_err(CmdError::from)
            .and_then(|report| {
                let d = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs();
                let mut file = File::create(format!("profile-{}.pb", d))?;
                let mut content = Vec::new();
                let profile = report.pprof()?;
                profile.write_to_vec(&mut content)?;
                file.write_all(&content)?;

                let file = File::create(format!("flamegraph-{}.svg", d))?;
                report.flamegraph(file)?;
                Ok(())
            })
            .err()
        {
            eprintln!("{} {}", "profiling error:".red(), err.msg)
        }
    }
}
