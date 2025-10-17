use log::info;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    InitializeParams, InitializeResult, InitializedParams, MessageType, ServerCapabilities,
    ServerInfo,
};
use tower_lsp::{Client, LspService, Server};

#[derive(Debug)]
struct RayLanguageServer {
    client: Client,
}

#[tower_lsp::async_trait]
impl tower_lsp::LanguageServer for RayLanguageServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        info!("initialize request: {params:#?}");

        Ok(InitializeResult {
            capabilities: ServerCapabilities::default(),
            server_info: Some(ServerInfo {
                name: "ray-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        let message = format!(
            "Ray Language Server {} ready",
            env!("CARGO_PKG_VERSION")
        );
        let _ = self
            .client
            .log_message(MessageType::INFO, message)
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        info!("shutdown request received");
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| RayLanguageServer { client });
    Server::new(stdin, stdout, socket).serve(service).await;
}
