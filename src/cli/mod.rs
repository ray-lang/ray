use std::{error::Error, fs::File, io::Write, process};

use clap::{Parser, Subcommand, builder::styling};
use colored::Colorize;
use pprof::protos::Message;
use ray_core::pathlib::RayPaths;
use ray_driver::{AnalyzeOptions, BuildOptions, GlobalOptions};
use ray_shared::logger;

mod analyze;
mod backend;
mod build;
mod install;
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
    /// Install a toolchain
    Install(install::InstallOptions),
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

    if ray_paths.is_none() && !matches!(cli.cmd, Command::Install(_)) {
        eprintln!(
            "error: unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
        );
        process::exit(1);
    }

    let prof = if cli.global_options.profile {
        Some(pprof::ProfilerGuard::new(100).unwrap())
    } else {
        None
    };

    match cli.cmd {
        Command::Build(options) => {
            let paths = ray_paths
                .clone()
                .expect("ray_paths validated for build command");
            build::action(paths, options, cli.global_options)
        }
        Command::Analyze(options) => {
            let paths = ray_paths
                .clone()
                .expect("ray_paths validated for analyze command");
            analyze::action(paths, options, cli.global_options)
        }
        Command::Lsp(options) => lsp::action(options),
        Command::Install(options) => install::action(ray_paths, options, cli.global_options),
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
