use crate::driver::{BuildOptions, CSTOptions, Driver};
use crate::pathlib::FilePath;

use colored::{Color, ColoredString, Colorize};
use log::Level;
use pprof::protos::Message;
use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use structopt::StructOpt;

mod build;
mod cst;

#[derive(Debug, StructOpt)]
pub struct Cli {
    #[structopt(
        name = "root-path",
        long = "root-path",
        env = "RAY_PATH",
        help = "root path for ray libraries and sources",
        long_help = "If not provided, it will default to `$HOME/.ray`. If that path is inaccessible, then /opt/ray will be used.",
        global = true
    )]
    ray_path: Option<FilePath>,

    #[structopt(
        long, env = "LOG_LEVEL",
        help = "Sets the log level",
        default_value = "info",
        possible_values = &["off", "error", "warn", "info", "debug"],
        global = true
    )]
    log_level: log::LevelFilter,

    #[structopt(
        long,
        help = "Runs in profiling mode, outputting to profile-<DATE>.pb",
        global = true
    )]
    profile: bool,

    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(Debug, StructOpt)]
pub enum Command {
    Build(BuildOptions),
    ParseCST(CSTOptions),
}

pub struct CmdError {
    msg: String,
}

impl<E: Error> From<E> for CmdError {
    fn from(e: E) -> Self {
        CmdError { msg: e.to_string() }
    }
}

pub fn run() {
    // get the subcommand
    let cli: Cli = Cli::from_args();

    // set up logging
    fern::Dispatch::new()
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
        .level(cli.log_level)
        .chain(io::stderr())
        .apply()
        .unwrap();

    // get the ray_path
    let ray_path = if let Some(p) = cli.ray_path {
        p
    } else {
        match home::home_dir() {
            Some(h) => FilePath::from(h) / ".ray",
            None => FilePath::from("/opt/ray"),
        }
    };

    let prof = if cli.profile {
        Some(pprof::ProfilerGuard::new(100).unwrap())
    } else {
        None
    };

    let mut driver = Driver::new(ray_path);
    match cli.cmd {
        Command::Build(options) => build::action(&mut driver, options),
        Command::ParseCST(options) => cst::action(&mut driver, options),
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
                profile.encode(&mut content)?;
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
