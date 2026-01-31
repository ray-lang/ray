use std::error::Error;

use tower_lsp::{LspService, Server};

mod diagnostics;
mod helpers;
mod semantic_tokens;
mod server;
mod symbols;

use server::RayLanguageServer;

pub async fn run_stdio_server() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| RayLanguageServer::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
}

pub fn run_stdio_server_blocking() -> Result<(), Box<dyn Error + Send + Sync>> {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|err| Box::new(err) as Box<dyn Error + Send + Sync>)?;
    runtime.block_on(run_stdio_server());
    Ok(())
}
