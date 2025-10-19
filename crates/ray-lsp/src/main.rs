use std::{
    collections::HashMap,
    path::PathBuf,
    sync::atomic::{AtomicBool, Ordering},
};

use log::{info, warn};
use tower_lsp::{
    Client, LspService, Server,
    jsonrpc::Result,
    lsp_types::{
        DidChangeConfigurationParams, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
        DidOpenTextDocumentParams, InitializeParams, InitializeResult, InitializedParams,
        MessageType, SemanticTokens, SemanticTokensFullOptions, SemanticTokensOptions,
        SemanticTokensParams, SemanticTokensResult, SemanticTokensServerCapabilities,
        ServerCapabilities, ServerInfo,
    },
};

mod diagnostics;
mod semantic_tokens;

use ray::pathlib::FilePath;
use serde_json::Value;

use crate::semantic_tokens::pretty_dump;

#[derive(Clone)]
struct DocumentData {
    text: String,
    version: Option<i32>,
}

impl DocumentData {
    fn new(text: String, version: Option<i32>) -> Self {
        Self { text, version }
    }
}

struct RayLanguageServer {
    client: Client,
    documents: tokio::sync::RwLock<HashMap<tower_lsp::lsp_types::Url, DocumentData>>,
    workspace_root: tokio::sync::RwLock<Option<FilePath>>,
    toolchain_root: tokio::sync::RwLock<Option<FilePath>>,
    missing_toolchain_warning_emitted: AtomicBool,
}

#[tower_lsp::async_trait]
impl tower_lsp::LanguageServer for RayLanguageServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        info!("initialize request: {params:#?}");

        self.update_workspace_root(&params).await;
        self.update_toolchain_root(params.initialization_options.as_ref())
            .await;

        let semantic_tokens_capability =
            SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
                legend: semantic_tokens::legend(),
                full: Some(SemanticTokensFullOptions::Bool(true)),
                range: Some(false),
                ..Default::default()
            });

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                semantic_tokens_provider: Some(semantic_tokens_capability),
                ..ServerCapabilities::default()
            },
            server_info: Some(ServerInfo {
                name: "ray-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        let message = format!("Ray Language Server {} ready", env!("CARGO_PKG_VERSION"));
        let _ = self.client.log_message(MessageType::INFO, message).await;
    }

    async fn shutdown(&self) -> Result<()> {
        info!("shutdown request received");
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = Some(params.text_document.version);

        self.documents
            .write()
            .await
            .insert(uri.clone(), DocumentData::new(text, version));

        let message = format!("Opened document {uri}");
        let _ = self.client.log_message(MessageType::INFO, message).await;

        self.publish_diagnostics(&uri).await;
        self.request_semantic_tokens_refresh().await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            let mut documents = self.documents.write().await;
            let entry = documents
                .entry(params.text_document.uri.clone())
                .or_insert_with(|| {
                    DocumentData::new(String::new(), Some(params.text_document.version))
                });
            entry.text = change.text;
            entry.version = Some(params.text_document.version);

            drop(documents);
            self.publish_diagnostics(&params.text_document.uri).await;
            self.request_semantic_tokens_refresh().await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        {
            self.documents
                .write()
                .await
                .remove(&params.text_document.uri);
        }

        // Clear diagnostics for the closed document
        let _ = self
            .client
            .publish_diagnostics(params.text_document.uri.clone(), Vec::new(), None)
            .await;

        self.request_semantic_tokens_refresh().await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        self.update_toolchain_root(Some(&params.settings)).await;
        self.republish_all_diagnostics().await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        self.log(format!(
            "[server] semTokens request {}",
            params.text_document.uri
        ))
        .await;

        let uri = params.text_document.uri;
        let mut text = {
            let documents = self.documents.read().await;
            documents.get(&uri).map(|doc| doc.text.clone())
        };

        if text.is_none() {
            text = uri
                .to_file_path()
                .ok()
                .and_then(|path| std::fs::read_to_string(path).ok());
        }

        self.log(format!(
            "[server] semantic tokens request for {} (has text: {})",
            uri,
            text.as_ref().map(|s| !s.is_empty()).unwrap_or(false),
        ))
        .await;

        let tokens = text
            .as_ref()
            .map(|source| semantic_tokens::semantic_tokens(source))
            .unwrap_or_else(|| SemanticTokens {
                result_id: None,
                data: Vec::new(),
            });

        // wherever you convert your syntax tree to SemanticToken entries
        let mut count = 0usize;
        let mut last_line = 0u32;
        let mut last_abs = (0u32, 0u32);

        for t in tokens.data.iter() {
            // assert strictly increasing positions
            let abs_line = last_abs.0 + t.delta_line;
            let abs_col = if t.delta_line == 0 {
                last_abs.1 + t.delta_start
            } else {
                t.delta_start
            };

            if t.length == 0 {
                self.log(format!(
                    "[server] zero-length token at L{}:{}",
                    abs_line, abs_col
                ))
                .await;
            }
            if abs_line < last_line || (abs_line == last_line && abs_col < last_abs.1) {
                self.log(format!(
                    "[server] out-of-order token at L{}:{} (prev L{}:{})",
                    abs_line, abs_col, last_abs.0, last_abs.1
                ))
                .await;
            }

            last_line = abs_line;
            last_abs = (abs_line, abs_col);
            count += 1;

            if count <= 20 {
                self.log(format!(
                    "[server] #{:03} L{}:{} len={} typeIdx={} modsBits={}",
                    count, abs_line, abs_col, t.length, t.token_type, t.token_modifiers_bitset
                ))
                .await;
            }
        }
        self.log(format!("[server] built {} tokens total", count))
            .await;

        let legend = semantic_tokens::legend();
        let source_text = text.unwrap_or_default();
        let dump = pretty_dump(&tokens.data, &source_text, &legend);
        self.log(dump).await;

        Ok(Some(SemanticTokensResult::Tokens(tokens)))
    }
}

impl RayLanguageServer {
    async fn request_semantic_tokens_refresh(&self) {
        if let Err(err) = self.client.semantic_tokens_refresh().await {
            warn!("failed requesting semantic token refresh: {err}");
        }
    }

    async fn log<S: ToString>(&self, message: S) {
        let _ = self
            .client
            .log_message(MessageType::INFO, message.to_string())
            .await;
    }

    async fn update_workspace_root(&self, params: &InitializeParams) {
        let root_path = params
            .root_uri
            .as_ref()
            .and_then(|uri| uri.to_file_path().ok())
            .or_else(|| {
                params
                    .workspace_folders
                    .as_ref()
                    .and_then(|folders| folders.first())
                    .and_then(|folder| folder.uri.to_file_path().ok())
            })
            .or_else(|| std::env::current_dir().ok());

        if let Some(path) = root_path {
            let mut root = self.workspace_root.write().await;
            *root = Some(FilePath::from(path));
        }
    }

    async fn update_toolchain_root(&self, value: Option<&Value>) {
        let parsed = value.and_then(parse_toolchain_path);
        let mut toolchain = self.toolchain_root.write().await;
        *toolchain = parsed;
        if toolchain.is_some() {
            self.missing_toolchain_warning_emitted
                .store(false, Ordering::SeqCst);
        }
    }

    async fn publish_diagnostics(&self, uri: &tower_lsp::lsp_types::Url) {
        let (text, version) = {
            let documents = self.documents.read().await;
            match documents.get(uri) {
                Some(document) => (document.text.clone(), document.version),
                None => {
                    let _ = self
                        .client
                        .publish_diagnostics(uri.clone(), Vec::new(), None)
                        .await;
                    return;
                }
            }
        };

        let workspace_root = {
            let root = self.workspace_root.read().await;
            root.clone()
        };

        let toolchain_root = {
            let root = self.toolchain_root.read().await;
            root.clone()
        };

        let diagnostics =
            diagnostics::collect(uri, &text, workspace_root.as_ref(), toolchain_root.as_ref());
        match diagnostics {
            diagnostics::CollectResult::Diagnostics(diagnostics) => {
                self.missing_toolchain_warning_emitted
                    .store(false, Ordering::SeqCst);
                let _ = self
                    .client
                    .publish_diagnostics(uri.clone(), diagnostics, version)
                    .await;
            }
            diagnostics::CollectResult::ToolchainMissing => {
                let first_warning = !self
                    .missing_toolchain_warning_emitted
                    .swap(true, Ordering::SeqCst);
                if first_warning {
                    let message =
                        "Ray toolchain not found; analyzer diagnostics disabled".to_string();
                    warn!("{message}");
                    let _ = self
                        .client
                        .show_message(MessageType::WARNING, message.clone())
                        .await;
                    let _ = self.client.log_message(MessageType::WARNING, message).await;
                }
                let _ = self
                    .client
                    .publish_diagnostics(uri.clone(), Vec::new(), version)
                    .await;
            }
        }
    }

    async fn republish_all_diagnostics(&self) {
        let uris: Vec<_> = {
            let documents = self.documents.read().await;
            documents.keys().cloned().collect()
        };

        for uri in uris {
            self.publish_diagnostics(&uri).await;
        }
    }
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| RayLanguageServer {
        client,
        documents: tokio::sync::RwLock::new(HashMap::new()),
        workspace_root: tokio::sync::RwLock::new(None),
        toolchain_root: tokio::sync::RwLock::new(None),
        missing_toolchain_warning_emitted: AtomicBool::new(false),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

fn parse_toolchain_path(value: &Value) -> Option<FilePath> {
    match value {
        Value::Null => None,
        Value::String(s) => to_filepath(s),
        Value::Object(map) => map
            .get("toolchainPath")
            .and_then(Value::as_str)
            .and_then(to_filepath)
            .or_else(|| {
                map.get("toolchain_path")
                    .and_then(Value::as_str)
                    .and_then(to_filepath)
            }),
        _ => None,
    }
}

fn to_filepath(s: &str) -> Option<FilePath> {
    if s.trim().is_empty() {
        None
    } else {
        Some(FilePath::from(PathBuf::from(s)))
    }
}
