use std::{error::Error, fs::File, io::Write, process};

use clap::{Parser, Subcommand, builder::styling};
use colored::Colorize;
use ray_core::pathlib::RayPaths;
use ray_driver::{AnalyzeOptions, BuildOptions, Driver, GlobalOptions};
use ray_shared::logger;

mod analyze;
mod build;
mod lsp;

const STYLES: styling::Styles = styling::Styles::styled()
    .header(styling::AnsiColor::Green.on_default().bold())
    .usage(styling::AnsiColor::Green.on_default().bold())
    .literal(styling::AnsiColor::Blue.on_default().bold())
    .placeholder(styling::AnsiColor::Cyan.on_default());

#[derive(Debug, Parser)]
#[command(
    color = clap::ColorChoice::Auto,
    styles = STYLES,
)]
pub struct Cli {
    #[command(flatten)]
    global_options: GlobalOptions,

    #[command(subcommand)]
    cmd: Command,
}

#[derive(Debug, Subcommand)]
pub enum Command {
    /// Build a module or file into a binary, or library
    Build(BuildOptions),
    /// Analyze a module or file
    Analyze(AnalyzeOptions),
    /// Run the language server
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
            _ => { /* ignore */ }
        }

        None
    }
}

pub fn run() {
    // get the subcommand
    let cli = Cli::parse();

    // set up logging
    let mut dispatch = logger::base(cli.global_options.log_level);

    if let Some(sub_logger) = cli.cmd.configure_logger() {
        dispatch = dispatch.chain(sub_logger)
    } else {
        dispatch = logger::stderr(dispatch);
    }

    dispatch.apply().unwrap();

    // get the ray_path
    let explicit_root = cli.global_options.root_path.clone();
    let discovered_paths = RayPaths::discover(explicit_root.clone(), None);
    let ray_paths = discovered_paths
        .clone()
        .or_else(|| explicit_root.clone().map(RayPaths::new));

    if ray_paths.is_none() {
        eprintln!(
            "error: unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
        );
        process::exit(1);
    }

    match cli.cmd {
        Command::Build(options) => {
            let mut driver = Driver::new(ray_paths.unwrap());
            build::action(&mut driver, options);
        }
        Command::Analyze(options) => {
            let mut driver = Driver::new(ray_paths.unwrap());
            analyze::action(&mut driver, options);
        }
        Command::Lsp(options) => lsp::action(options),
    }
}
