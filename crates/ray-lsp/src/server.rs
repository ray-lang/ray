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
        DidOpenTextDocumentParams, DidSaveTextDocumentParams, GotoDefinitionParams,
        GotoDefinitionResponse, Hover, HoverContents, HoverParams, InitializeParams,
        InitializeResult, InitializedParams, Location, MarkupContent, MarkupKind, MessageType,
        Position, SemanticTokens, SemanticTokensFullOptions, SemanticTokensOptions,
        SemanticTokensParams, SemanticTokensResult, SemanticTokensServerCapabilities,
        ServerCapabilities, ServerInfo, TextDocumentSyncCapability, TextDocumentSyncOptions, Url,
    },
};

use ray_frontend::queries::{
    bindings::local_binding_names,
    display::{def_display_info, display_ty},
    locations::{self, find_at_position},
    resolve::name_resolutions,
    symbols::symbol_targets,
    typecheck::ty_of,
};
use ray_shared::{
    file_id::FileId,
    pathlib::{FilePath, RayPaths},
    resolution::{DefTarget, Resolution},
    symbol::SymbolIdentity,
};
use serde_json::Value;

use crate::{
    diagnostics::{self, AnalysisSnapshotData},
    helpers::{
        filepath_to_uri, is_core_library_uri, parse_toolchain_path, span_to_range, uri_to_filepath,
    },
    semantic_tokens::{self, pretty_dump},
    symbols::{ResolvedSymbol, resolve_symbol_at_position},
    workspace::{LspWorkspace, WorkspaceManager},
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
    workspace_manager: RwLock<WorkspaceManager>,
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
        self.init_workspaces().await;

        let text_sync = Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(tower_lsp::lsp_types::TextDocumentSyncKind::FULL),
                will_save: Some(false),
                will_save_wait_until: Some(false),
                save: Some(tower_lsp::lsp_types::TextDocumentSyncSaveOptions::Supported(true)),
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

        self.store_document(&uri, text.clone(), version).await;

        // Apply overlay to incremental workspace
        if let Some(canonical) = Self::resolve_file_path(&uri) {
            let mut manager = self.workspace_manager.write().await;
            match manager.workspace_for_file_or_create(&canonical) {
                Ok(ws) => {
                    if let Some(file_id) = ws.file_id(&canonical) {
                        ws.apply_overlay(file_id, text.clone());
                    } else {
                        ws.add_file(&canonical, text.clone());
                    }
                }
                Err(e) => {
                    log::warn!(
                        "didOpen: failed to find/create workspace for {}: {}",
                        uri,
                        e
                    );
                }
            }
        }

        let message = format!("Opened document {uri}");
        let _ = self.client.log_message(MessageType::INFO, message).await;

        self.publish_diagnostics(&uri).await;
        self.schedule_semantic_tokens_refresh().await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            let uri = params.text_document.uri.clone();
            let version = Some(params.text_document.version);

            self.store_document(&uri, change.text.clone(), version)
                .await;

            self.log(format!(
                "[server] did_change: version={} len={}",
                version.unwrap_or_default(),
                change.text.len()
            ))
            .await;

            // Apply overlay to incremental workspace
            self.with_workspace_file(&uri, |ws: &LspWorkspace, file_id| {
                ws.apply_overlay(file_id, change.text);
            })
            .await;

            self.publish_diagnostics(&params.text_document.uri).await;
            self.schedule_semantic_tokens_refresh().await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = &params.text_document.uri;

        {
            self.documents.write().await.remove(uri);
        }
        {
            self.diagnostics_published_version.write().await.remove(uri);
        }

        // Revert overlay to disk content in the incremental workspace
        self.with_workspace_file(uri, |ws: &LspWorkspace, file_id| {
            if let Err(e) = ws.revert_to_disk(file_id) {
                log::warn!("didClose: failed to revert {}: {}", uri, e);
            }
        })
        .await;

        // Clear diagnostics for the closed document
        let _ = self
            .client
            .publish_diagnostics(uri.clone(), Vec::new(), None)
            .await;

        self.schedule_semantic_tokens_refresh().await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = &params.text_document.uri;

        // Re-read from disk to capture post-save hooks/formatters, then flush cache.
        self.with_workspace_file(uri, |ws: &LspWorkspace, file_id| {
            if let Err(e) = ws.revert_to_disk(file_id) {
                log::warn!("didSave: failed to re-read {}: {}", uri, e);
            }
            ws.flush();
        })
        .await;

        self.publish_diagnostics(uri).await;
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

        let result = self
            .with_workspace_file_map(&uri, |ws: &LspWorkspace, file_id| {
                let db = &*ws.db;

                // Find the AST node at the cursor position
                let node_id = find_at_position(
                    db,
                    file_id,
                    position.line as usize,
                    position.character as usize,
                )?;

                // Get the span for the hover range
                let span = locations::span_of(db, node_id);

                // Look up what this node resolves to
                let resolutions = name_resolutions(db, file_id);
                let resolution = resolutions.get(&node_id).cloned();

                let hover_content = match resolution {
                    Some(Resolution::Def(target)) => {
                        // Definition reference: use def_display_info for provenance chain
                        def_display_info(db, target).map(|info| {
                            format_hover_markdown(&info.signatures, info.doc.as_deref())
                        })
                    }
                    Some(Resolution::TypeParam(type_param_id)) => {
                        // Type parameter: show the owning definition's provenance
                        let owner_target = DefTarget::Workspace(type_param_id.owner);
                        def_display_info(db, owner_target).map(|info| {
                            format_hover_markdown(&info.signatures, info.doc.as_deref())
                        })
                    }
                    Some(Resolution::Local(local_id)) => {
                        // Local binding: show name: type
                        let binding_names = local_binding_names(db, file_id);
                        let name = binding_names.get(&local_id);
                        let ty = ty_of(db, node_id).map(|ty| display_ty(db, local_id.owner, &ty));
                        match (name, ty) {
                            (Some(name), Some(ty)) => {
                                Some(format!("```ray\n{}: {}\n```", name, ty))
                            }
                            (None, Some(ty)) => Some(format!("```ray\n{}\n```", ty)),
                            (Some(name), None) => Some(format!("```ray\n{}\n```", name)),
                            (None, None) => None,
                        }
                    }
                    Some(Resolution::Error { .. }) | None => {
                        // Try symbol_targets for field access, method calls, etc.
                        let targets = symbol_targets(db, node_id);
                        let def_target = targets.iter().find_map(|t| match &t.identity {
                            SymbolIdentity::Def(target) => Some(target.clone()),
                            _ => None,
                        });

                        if let Some(target) = def_target {
                            def_display_info(db, target).map(|info| {
                                format_hover_markdown(&info.signatures, info.doc.as_deref())
                            })
                        } else {
                            // Fallback: show the inferred type if available
                            let ty =
                                ty_of(db, node_id).map(|ty| display_ty(db, node_id.owner, &ty));
                            ty.map(|ty| format!("```ray\n{}\n```", ty))
                        }
                    }
                };

                let range = span.map(span_to_range);
                hover_content.map(|content| (content, range))
            })
            .await
            .flatten();

        match result {
            Some((markdown, range)) => {
                let contents = HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: markdown,
                });
                Ok(Some(Hover { contents, range }))
            }
            None => Ok(None),
        }
    }
}

/// Format hover content as markdown from a list of signature strings.
///
/// Each signature is wrapped in a ```ray code block. Signatures are
/// separated by horizontal rules for visual hierarchy (outermost
/// container first, innermost definition last).
fn format_hover_markdown(signatures: &[String], doc: Option<&str>) -> String {
    let mut parts: Vec<String> = signatures
        .iter()
        .map(|sig| format!("```ray\n{}\n```", sig))
        .collect();

    if let Some(doc) = doc {
        parts.push(doc.to_string());
    }

    parts.join("\n\n---\n\n")
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
            workspace_manager: RwLock::new(WorkspaceManager::new()),
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

    /// Resolve a URI to a canonical file path.
    fn resolve_file_path(uri: &Url) -> Option<FilePath> {
        let filepath = uri_to_filepath(uri)?;
        Some(filepath.canonicalize().unwrap_or(filepath))
    }

    /// Store a document's text and version in the in-memory document map.
    async fn store_document(&self, uri: &Url, text: String, version: Option<i32>) {
        self.documents
            .write()
            .await
            .insert(uri.clone(), DocumentData::new(text, version));
    }

    /// Resolve a URI, acquire a read lock on the workspace manager, look up
    /// the workspace and FileId, and pass them to a closure.
    async fn with_workspace_file(&self, uri: &Url, f: impl FnOnce(&LspWorkspace, FileId)) {
        if let Some(canonical) = Self::resolve_file_path(uri) {
            let manager = self.workspace_manager.read().await;
            if let Some((ws, file_id)) = manager.lookup_file(&canonical) {
                f(ws, file_id);
            }
        }
    }

    /// Like `with_workspace_file`, but returns a value from the closure.
    async fn with_workspace_file_map<R>(
        &self,
        uri: &Url,
        f: impl FnOnce(&LspWorkspace, FileId) -> R,
    ) -> Option<R> {
        let canonical = Self::resolve_file_path(uri)?;
        let manager = self.workspace_manager.read().await;
        let (ws, file_id) = manager.lookup_file(&canonical)?;
        Some(f(ws, file_id))
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

    /// Initialize incremental workspaces by scanning for ray.toml files.
    ///
    /// Called during `initialize` after workspace root and toolchain root are known.
    /// Discovers RayPaths from the toolchain root, then scans the workspace root
    /// for ray.toml files, creating a Database-backed workspace for each.
    async fn init_workspaces(&self) {
        let workspace_root = self.workspace_root.read().await.clone();
        let toolchain_root = self.toolchain_root.read().await.clone();

        let Some(ws_root) = workspace_root else {
            log::info!("no workspace root; skipping workspace initialization");
            return;
        };

        let ray_paths = match RayPaths::discover(toolchain_root, Some(&ws_root)) {
            Some(paths) => paths,
            None => {
                log::warn!("RayPaths not found; skipping workspace initialization");
                return;
            }
        };

        let mut manager = self.workspace_manager.write().await;
        manager.initialize(&ws_root, ray_paths);

        log::info!(
            "initialized {} workspace(s) under {}",
            manager.workspace_count(),
            ws_root
        );
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
            "[server] lookup_symbol_targets_at: snapshot version={:?} module={} defs={}",
            snapshot.version,
            snapshot.data.module_path,
            snapshot.data.definitions.len(),
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
