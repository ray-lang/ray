use std::{
    collections::{HashMap, HashSet},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use log;
use tokio::sync::{OwnedSemaphorePermit, RwLock, Semaphore};
use tower_lsp::{
    Client,
    jsonrpc::Result,
    lsp_types::{
        DidChangeConfigurationParams, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
        DidOpenTextDocumentParams, GotoDefinitionParams, GotoDefinitionResponse, Hover,
        HoverContents, HoverParams, InitializeParams, InitializeResult, InitializedParams,
        Location, MarkupContent, MarkupKind, MessageType, Position, SemanticTokens,
        SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensParams,
        SemanticTokensResult, SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo,
        TextDocumentSyncCapability, TextDocumentSyncOptions, Url,
    },
};

use ray_core::libgen;
use ray_core::libgen::DefinitionKind;
use ray_shared::span::Span;
use ray_shared::{node_id::NodeId, pathlib::FilePath};
use serde_json::Value;

use crate::{
    diagnostics::{self, AnalysisSnapshotData},
    helpers::{
        filepath_to_uri, is_core_library_uri, parse_toolchain_path, span_to_range, uri_to_filepath,
    },
    semantic_tokens::{self, pretty_dump},
    symbols::{ResolvedSymbol, resolve_symbol_at_position},
};

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

pub(crate) struct RayLanguageServer {
    client: Client,
    documents: RwLock<HashMap<Url, DocumentData>>,
    diagnostics_published_version: RwLock<HashMap<Url, Option<i32>>>,
    analysis_cache: RwLock<HashMap<Url, AnalysisSnapshot>>,
    workspace_root: RwLock<Option<FilePath>>,
    toolchain_root: RwLock<Option<FilePath>>,
    missing_toolchain_warning_emitted: AtomicBool,
    semantic_refresh_pending: Arc<AtomicBool>,
    semantic_compute: Arc<Semaphore>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct AnalysisSnapshot {
    version: Option<i32>,
    data: Arc<AnalysisSnapshotData>,
}

#[tower_lsp::async_trait]
impl tower_lsp::LanguageServer for RayLanguageServer {
    async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
        log::info!("initialize request: {params:#?}");

        self.update_workspace_root(&params).await;
        self.update_toolchain_root(params.initialization_options.as_ref())
            .await;

        let text_sync = Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(tower_lsp::lsp_types::TextDocumentSyncKind::FULL),
                will_save: Some(false),
                will_save_wait_until: Some(false),
                save: Some(tower_lsp::lsp_types::TextDocumentSyncSaveOptions::Supported(false)),
            },
        ));

        let semantic_tokens_capability =
            SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
                legend: semantic_tokens::legend(),
                full: Some(SemanticTokensFullOptions::Bool(true)),
                range: Some(false),
                ..Default::default()
            });

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: text_sync,
                semantic_tokens_provider: Some(semantic_tokens_capability),
                hover_provider: Some(tower_lsp::lsp_types::HoverProviderCapability::Simple(true)),
                definition_provider: Some(tower_lsp::lsp_types::OneOf::Left(true)),
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
        log::info!("shutdown request received");
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
        self.schedule_semantic_tokens_refresh().await;
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

            let msg = format!(
                "[server] did_change: version={} len={}",
                entry.version.unwrap_or_default(),
                entry.text.len()
            );
            self.log(msg).await;

            drop(documents);
            self.publish_diagnostics(&params.text_document.uri).await;
            self.schedule_semantic_tokens_refresh().await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        {
            self.documents
                .write()
                .await
                .remove(&params.text_document.uri);
        }
        {
            self.diagnostics_published_version
                .write()
                .await
                .remove(&params.text_document.uri);
        }

        // Clear diagnostics for the closed document
        let _ = self
            .client
            .publish_diagnostics(params.text_document.uri.clone(), Vec::new(), None)
            .await;

        self.schedule_semantic_tokens_refresh().await;
    }

    async fn did_change_configuration(&self, params: DidChangeConfigurationParams) {
        self.update_toolchain_root(Some(&params.settings)).await;
        {
            self.diagnostics_published_version.write().await.clear();
        }
        self.republish_all_diagnostics().await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;

        let _permit: OwnedSemaphorePermit = self
            .semantic_compute
            .clone()
            .acquire_owned()
            .await
            .expect("semaphore acquire failed");

        self.log("[server] semTokens/full begin").await;

        let (text, start_version) = {
            let documents = self.documents.read().await;
            match documents.get(&uri) {
                Some(doc) => (Some(doc.text.clone()), doc.version),
                None => (None, None),
            }
        };

        let source_note = String::from("doc");

        if text.is_none() {
            // Do NOT fall back to disk content; it can be out-of-sync with the editor.
            // Instead, schedule a refresh and let the client re-request once we have in-memory text.
            self.log(
                "[server] semTokens/full no in-memory text; scheduling refresh & returning None",
            )
            .await;
            self.schedule_semantic_tokens_refresh().await;
            return Ok(None);
        }

        self.log(format!(
            "[server] semTokens/full src={} start_version={:?} len={}",
            source_note,
            start_version,
            text.as_ref().map(|s| s.len()).unwrap_or(0),
        ))
        .await;

        let tokens = text
            .as_ref()
            .map(|source| semantic_tokens::semantic_tokens(source))
            .unwrap_or_else(|| SemanticTokens {
                result_id: None,
                data: Vec::new(),
            });

        let built_count = tokens.data.len();
        let mut last_abs_line_hint: u32 = 0;
        for t in &tokens.data {
            last_abs_line_hint = last_abs_line_hint.saturating_add(t.delta_line);
        }
        self.log(format!(
            "[server] semTokens/full built_count={} last_abs_line_hint={}",
            built_count, last_abs_line_hint
        ))
        .await;

        // If the document version changed while we were computing tokens, drop this response
        // to avoid out-of-order coloring after edits. The client will request again.
        if start_version.is_some() {
            let current_version = {
                let documents = self.documents.read().await;
                documents.get(&uri).and_then(|d| d.version)
            };
            if current_version != start_version {
                self.log(format!(
                    "[server] semTokens/full DROP outdated: start={:?} current={:?}",
                    start_version, current_version
                ))
                .await;
                return Ok(None);
            }
        }
        // Version may also change during logging below; we re-check once more before returning.

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

            self.log(format!(
                "[server] #{:03} L{}:{} len={} typeIdx={} modsBits={}",
                count, abs_line, abs_col, t.length, t.token_type, t.token_modifiers_bitset
            ))
            .await;
        }
        self.log(format!("[server] built {} tokens total", count))
            .await;

        if log::log_enabled!(log::Level::Debug) {
            let legend = semantic_tokens::legend();
            let source_text = text.unwrap_or_default();
            let dump = pretty_dump(&tokens.data, &source_text, &legend);
            self.log(dump).await;
        }

        if start_version.is_some() {
            let current_version = {
                let documents = self.documents.read().await;
                documents.get(&uri).and_then(|d| d.version)
            };
            if current_version != start_version {
                self.log(format!(
                    "[server] semTokens/full DROP outdated (post-log): start={:?} current={:?}",
                    start_version, current_version
                ))
                .await;
                return Ok(None);
            }
        }
        Ok(Some(SemanticTokensResult::Tokens(tokens)))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some((_snapshot, resolved)) = self.lookup_symbol_targets_at(&uri, position).await
        else {
            return Ok(None);
        };

        self.log(format!(
            "[server] goto_definition: found source for node_id={} source_span={:?}",
            resolved.node_id, resolved.source.span
        ))
        .await;

        let symbol_targets = &resolved.symbol_targets;
        if symbol_targets.is_empty() {
            self.log(format!(
                "[server] goto_definition: no symbol target for node_id={}",
                resolved.node_id
            ))
            .await;
            return Ok(None);
        };

        let mut seen_locations = HashSet::new();
        let mut locations = Vec::new();

        for target in symbol_targets {
            let span = target.span;
            let Some(target_uri) = filepath_to_uri(&target.filepath) else {
                self.log(format!(
                    "[server] goto_definition: unable to convert filepath={} to URI",
                    target.filepath
                ))
                .await;
                continue;
            };

            let key = (target_uri.clone(), span);
            if !seen_locations.insert(key) {
                continue;
            }

            let range = span_to_range(span);
            locations.push(Location {
                uri: target_uri,
                range,
            });
        }

        if locations.is_empty() {
            self.log(format!(
                "[server] goto_definition: empty symbol target list for node_id={}",
                resolved.node_id
            ))
            .await;
            return Ok(None);
        }

        Ok(Some(GotoDefinitionResponse::Array(locations)))
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let Some((snapshot, resolved)) = self.lookup_symbol_targets_at(&uri, position).await else {
            return Ok(None);
        };

        self.log(format!(
            "[server] hover: found source for node_id={} source_span={:?}",
            resolved.node_id, resolved.source.span
        ))
        .await;

        let symbol_targets = &resolved.symbol_targets;
        if symbol_targets.is_empty() {
            self.log(format!(
                "[server] hover: no symbol target for node_id={}",
                resolved.node_id
            ))
            .await;
            return Ok(None);
        };

        let has_node_type = snapshot.data.node_type_info.contains_key(&resolved.node_id);
        let mut hover_entries: Vec<(String, Span)> = Vec::new();
        if let Some(span) = resolved.source.span {
            if let Some(entry) =
                node_type_hover_entry(&snapshot, resolved.node_id, symbol_targets, span)
            {
                hover_entries.push(entry);
            }
            hover_entries.extend(definition_hover_entries(
                &snapshot,
                resolved.node_id,
                symbol_targets,
                span,
                has_node_type,
            ));
        }

        if hover_entries.is_empty() {
            self.log(format!(
                "[server] hover: empty symbol target list for node_id={}",
                resolved.node_id
            ))
            .await;
            return Ok(None);
        }

        let range_span = hover_entries.first().map(|(_, span)| *span).unwrap();
        let range = span_to_range(range_span);

        let markdown = hover_entries
            .into_iter()
            .map(|(content, _)| content)
            .collect::<Vec<_>>()
            .join("\n\n---\n\n");

        let contents = HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: markdown,
        });

        let hover = Hover {
            contents,
            range: Some(range),
        };

        Ok(Some(hover))
    }
}

fn node_type_hover_entry(
    snapshot: &AnalysisSnapshot,
    node_id: NodeId,
    symbol_targets: &[ray_core::sema::SymbolTarget],
    span: Span,
) -> Option<(String, Span)> {
    let ty_info = snapshot.data.node_type_info.get(&node_id)?;
    let label = symbol_targets
        .first()
        .map(|target| target.path.to_short_name())
        .unwrap_or_default();
    let line = if label.is_empty() {
        ty_info.ty.clone()
    } else {
        format!("{}: {}", label, ty_info.ty)
    };
    Some((format!("```ray\n{}\n```", line), span))
}

fn definition_hover_entries(
    snapshot: &AnalysisSnapshot,
    node_id: NodeId,
    symbol_targets: &[ray_core::sema::SymbolTarget],
    span: Span,
    has_node_type: bool,
) -> Vec<(String, Span)> {
    let mut out: Vec<(String, Span)> = Vec::new();

    if let Some(record) = snapshot.data.definitions_by_id.get(&node_id) {
        if !should_skip_definition_record(has_node_type, &record.kind) {
            out.push((record.to_string(), span));
        }
    }

    let mut seen_paths = HashSet::new();
    for symbol_target in symbol_targets {
        let path_key = libgen::canonical_path_key(&symbol_target.path);
        if !seen_paths.insert(path_key.clone()) {
            continue;
        }

        match snapshot.data.definitions.get(&path_key) {
            Some(record) => {
                if should_skip_definition_record(has_node_type, &record.kind) {
                    continue;
                }
                out.push((record.to_string(), span));
            }
            None => {
                if has_node_type {
                    continue;
                }
                out.push((symbol_target.path.to_string(), span));
            }
        }
    }

    out
}

fn should_skip_definition_record(has_node_type: bool, kind: &DefinitionKind) -> bool {
    has_node_type
        && matches!(
            kind,
            DefinitionKind::Name { .. } | DefinitionKind::Variable { .. }
        )
}

impl RayLanguageServer {
    pub(crate) fn new(client: Client) -> Self {
        RayLanguageServer {
            client,
            documents: RwLock::new(HashMap::new()),
            diagnostics_published_version: RwLock::new(HashMap::new()),
            analysis_cache: RwLock::new(HashMap::new()),
            workspace_root: RwLock::new(None),
            toolchain_root: RwLock::new(None),
            missing_toolchain_warning_emitted: AtomicBool::new(false),
            semantic_refresh_pending: Arc::new(AtomicBool::new(false)),
            semantic_compute: Arc::new(Semaphore::new(1)), // limit concurrent semantic token computations
        }
    }

    async fn schedule_semantic_tokens_refresh(&self) {
        // Debounce: schedule at most one refresh every ~100ms
        if self
            .semantic_refresh_pending
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            let client = self.client.clone();
            let flag = Arc::clone(&self.semantic_refresh_pending);
            tokio::spawn(async move {
                use tokio::time::{Duration, sleep};
                sleep(Duration::from_millis(100)).await;
                let _ = client.semantic_tokens_refresh().await;
                flag.store(false, Ordering::SeqCst);
            });
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

    async fn publish_diagnostics(&self, uri: &Url) {
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

        // Skip duplicate publishes for the same version to avoid duplicate diagnostics and flicker.
        {
            let last = self.diagnostics_published_version.read().await;
            if let Some(prev) = last.get(uri) {
                if *prev == version {
                    self.log(format!(
                        "[server] diagnostics: skip duplicate publish for {:?}",
                        version
                    ))
                    .await;
                    return;
                }
            }
        }

        let workspace_root = {
            let root = self.workspace_root.read().await;
            root.clone()
        };

        // Prefer the in-workspace core sources when editing core itself.
        // Avoid trying to load a precompiled core.raylib, which causes IO errors and stale diagnostics.
        let toolchain_root = {
            let configured = { self.toolchain_root.read().await.clone() };
            if is_core_library_uri(uri) {
                // Signal the analyzer to not rely on an external/built core; use the open files instead.
                None
            } else {
                configured
            }
        };

        if is_core_library_uri(uri) {
            self.log(
                "[server] diagnostics: core file detected; using workspace core (no prebuilt)",
            )
            .await;
        }

        let diagnostics_result =
            diagnostics::collect(uri, &text, workspace_root.as_ref(), toolchain_root.as_ref());
        match diagnostics_result {
            diagnostics::CollectResult::Diagnostics {
                diagnostics,
                snapshot,
            } => {
                if let Some(snapshot) = snapshot {
                    let mut cache = self.analysis_cache.write().await;
                    cache.insert(
                        uri.clone(),
                        AnalysisSnapshot {
                            version,
                            data: Arc::new(snapshot),
                        },
                    );
                    if let Some(entry) = cache.get(&uri) {
                        self.log(format!(
                            "[server] diagnostics: cached snapshot: {:#?}",
                            entry.data
                        ))
                        .await;
                    }
                } else {
                    self.analysis_cache.write().await.remove(uri);
                }

                self.missing_toolchain_warning_emitted
                    .store(false, Ordering::SeqCst);
                // De-duplicate identical diagnostics (same message, range, severity, source).
                let mut seen = HashSet::new();
                let mut uniq = Vec::with_capacity(diagnostics.len());
                for d in diagnostics.into_iter() {
                    // Hash a stable Debug representation of severity to avoid private-field access.
                    // Using &Option<DiagnosticSeverity> here so we don't move it out of `d`.
                    let sev_dbg: Option<String> = d.severity.as_ref().map(|s| format!("{:?}", s));
                    let key = (
                        d.message.clone(),
                        d.range.start.line,
                        d.range.start.character,
                        d.range.end.line,
                        d.range.end.character,
                        sev_dbg,
                        d.source.clone(),
                    );
                    if seen.insert(key) {
                        uniq.push(d);
                    }
                }

                let _ = self
                    .client
                    .publish_diagnostics(uri.clone(), uniq, version)
                    .await;

                // Remember the last published version for this URI.
                {
                    let mut last = self.diagnostics_published_version.write().await;
                    last.insert(uri.clone(), version);
                }
            }
            diagnostics::CollectResult::ToolchainMissing => {
                self.analysis_cache.write().await.remove(uri);
                let first_warning = !self
                    .missing_toolchain_warning_emitted
                    .swap(true, Ordering::SeqCst);
                if first_warning {
                    let message =
                        "Ray toolchain not found; analyzer diagnostics disabled".to_string();
                    log::warn!("{message}");
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
                {
                    let mut last = self.diagnostics_published_version.write().await;
                    last.insert(uri.clone(), version);
                }
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

    async fn lookup_symbol_targets_at(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<(AnalysisSnapshot, ResolvedSymbol)> {
        // 1. snapshot
        let snapshot = {
            let cache = self.analysis_cache.read().await;
            cache.get(uri).cloned()
        }?;

        self.log(format!(
            "[server] lookup_symbol_targets_at: snapshot version={:?} module={} defs={} symbols={}",
            snapshot.version,
            snapshot.data.module_path,
            snapshot.data.definitions.len(),
            snapshot.data.symbol_map.len(),
        ))
        .await;

        // 2. filepath
        let filepath = uri_to_filepath(uri)?;
        let canon = filepath.canonicalize().unwrap_or(filepath.clone());

        // 3. node + source span in this file
        let resolved = resolve_symbol_at_position(
            &snapshot.data,
            &canon,
            position.line as usize,
            position.character as usize,
        )?;

        self.log(format!(
            "[server] lookup_symbol_targets_at: node_id={} source_span={:?}",
            resolved.node_id, resolved.source.span
        ))
        .await;

        Some((snapshot, resolved))
    }
}
