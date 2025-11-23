use std::process;

use clap::{Parser, Subcommand, builder::styling};
use ray_driver::{AnalyzeOptions, BuildOptions, Driver, GlobalOptions};
use ray_shared::logger;
use ray_shared::pathlib::RayPaths;

mod analyze;
mod bootstrap;
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
    /// Download and install the Ray toolchain
    Bootstrap(bootstrap::BootstrapOptions),
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

    match cli.cmd {
        Command::Bootstrap(options) => {
            let install_root = ray_paths.clone().unwrap_or_else(RayPaths::bootstrap_root);
            if let Err(err) = bootstrap::action(install_root, options) {
                eprintln!("error: {err:?}");
                process::exit(1);
            }
        }
        Command::Build(options) => {
            let ray_paths = ray_paths.unwrap_or_else(|| {
                eprintln!(
                    "error: unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
                );
                process::exit(1);
            });
            let mut driver = Driver::new(ray_paths);
            build::action(&mut driver, options);
        }
        Command::Analyze(options) => {
            let ray_paths = ray_paths.unwrap_or_else(|| {
                eprintln!(
                    "error: unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
                );
                process::exit(1);
            });
            let mut driver = Driver::new(ray_paths);
            analyze::action(&mut driver, options);
        }
        Command::Lsp(options) => lsp::action(options),
    }
}
