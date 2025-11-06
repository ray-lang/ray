use std::time::Instant;

use clap::{Parser, Subcommand};
use ray_core::pathlib::{FilePath, RayPaths};
use ray_driver::{AnalyzeOptions, BuildOptions, Driver};
use ray_shared::logger;

#[derive(Parser)]
#[command(name = "rayc", version, about = "Ray compiler")]
struct Cli {
    #[arg(
        value_name = "root-path",
        long = "root-path",
        env = "RAY_PATH",
        help = "Root path for ray libraries and sources",
        long_help = "If not provided, it will default to `$HOME/.ray`. If that path is inaccessible, then /opt/ray will be used.",
        global = true
    )]
    root_path: Option<FilePath>,

    #[arg(
        long,
        env = "LOG_LEVEL",
        help = "Sets the log level",
        default_value = "info",
        hide = true,
        global = true
    )]
    log_level: log::LevelFilter,

    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Debug, Subcommand)]
enum Cmd {
    Build(BuildOptions),
    Analyze(AnalyzeOptions),
}

fn main() {
    let args = Cli::parse();
    logger::init(args.log_level);

    let Some(paths) = RayPaths::discover(args.root_path, None) else {
        log::error!(
            "unable to locate Ray toolchain. Set --root-path or RAY_PATH to a directory containing lib/core and wasi-sysroot/include."
        );
        std::process::exit(1);
    };

    let mut driver = Driver::new(paths);
    match args.cmd {
        Cmd::Build(options) => {
            let start_time = Instant::now();
            log::info!("building for {}", options.get_target());
            match driver.build(options) {
                Err(errs) => {
                    driver.emit_errors(errs);
                    log::error!("{} errors emitted", driver.errors_emitted);
                    return;
                }
                _ => (),
            }

            // TODO: a prettier output
            let elapsed = start_time.elapsed();
            log::info!("compiled in {:?}", elapsed);
        }
        Cmd::Analyze(options) => {
            let report = driver.analyze(options);
            report.emit();
        }
    }
}
