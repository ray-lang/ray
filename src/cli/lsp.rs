use std::{process, str::FromStr};

use clap::StructOpt;
use log::error;
use ray_core::pathlib::FilePath;
use ray_driver::Driver;

#[derive(Debug, Clone, Copy)]
pub enum LspTransport {
    Stdio,
    // Tcp, // reserved for future use
    // Daemon,
}

#[derive(Debug, StructOpt)]
pub struct LspOptions {
    #[clap(
        long = "transport",
        default_value = "stdio",
        action = clap::ArgAction::Set,
        help = "Select the transport mechanism used by the language server"
    )]
    pub transport: LspTransport,

    #[clap(
        long = "log-file",
        action = clap::ArgAction::Set,
        help = "Write language server logs to the specified file"
    )]
    pub log_file: Option<FilePath>,
}

impl FromStr for LspTransport {
    type Err = String;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "stdio" => Ok(LspTransport::Stdio),
            // "tcp" => Ok(LspTransport::Tcp),
            // "daemon" => Ok(LspTransport::Daemon),
            other => Err(format!("unsupported transport `{}`", other)),
        }
    }
}

pub(super) fn action(_driver: &mut Driver, options: LspOptions) {
    match options.transport {
        LspTransport::Stdio => {
            log::info!("starting LSP server");
            if let Err(err) = ray_lsp::run_stdio_server_blocking() {
                error!("language server terminated with an error: {}", err);
                process::exit(1);
            }
        }
    }
}
