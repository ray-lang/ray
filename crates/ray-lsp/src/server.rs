use std::{
    collections::{HashMap, HashSet},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use log;
use tokio::{
    sync::{OwnedSemaphorePermit, RwLock, Semaphore},
    time::{Duration, sleep},
};
use tower_lsp::{
    Client,
    jsonrpc::Result,
    lsp_types::{
        CompletionItem, CompletionItemKind, CompletionOptions, CompletionParams,
        CompletionResponse, DidChangeConfigurationParams, DidChangeTextDocumentParams,
        DidCloseTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
        GotoDefinitionParams, GotoDefinitionResponse, Hover, HoverContents, HoverParams,
        InitializeParams, InitializeResult, InitializedParams, Location, MarkupContent, MarkupKind,
        MessageType, SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensParams,
        SemanticTokensResult, SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo,
        TextDocumentSyncCapability, TextDocumentSyncOptions, Url,
    },
};

use ray_frontend::queries::{
    bindings::{local_binding_definitions, local_binding_names},
    completion::{CompletionKind, completion_context},
    defs::{SourceLocation, def_header, definition_record},
    diagnostics::file_diagnostics,
    display::{def_display_info, display_library_ty, display_ty},
    exports::{ExportedItem, module_def_index},
    items::associated_items,
    locations::{self, find_at_position},
    methods::methods_for_type,
    resolve::name_resolutions,
    semantic_tokens::semantic_tokens as query_semantic_tokens,
    symbols::symbol_targets,
    typecheck::{def_scheme, ty_of},
    workspace::{FileMetadata, FileSource},
};
use ray_frontend::query::Database;
use ray_shared::{
    def::DefKind,
    file_id::FileId,
    pathlib::{FilePath, RayPaths},
    resolution::{DefTarget, Resolution},
    scope::ScopeEntry,
    span::Span,
    symbol::SymbolIdentity,
    ty::Ty,
};
use serde_json::Value;

use crate::{
    diagnostics,
    helpers::{
        filepath_to_uri, lsp_position_to_pos, parse_toolchain_path, span_to_range, uri_to_filepath,
    },
    semantic_tokens,
    workspace::{LspWorkspace, WorkspaceManager},
};

#[derive(Clone)]
struct DocumentData {
    version: Option<i32>,
}

impl DocumentData {
    fn new(version: Option<i32>) -> Self {
        Self { version }
    }
}

pub(crate) struct RayLanguageServer {
    client: Client,
    documents: RwLock<HashMap<Url, DocumentData>>,
    diagnostics_published_version: RwLock<HashMap<Url, Option<i32>>>,
    workspace_root: RwLock<Option<FilePath>>,
    toolchain_root: RwLock<Option<FilePath>>,
    workspace_manager: RwLock<WorkspaceManager>,
    semantic_refresh_pending: Arc<AtomicBool>,
    semantic_compute: Arc<Semaphore>,
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
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                    ..CompletionOptions::default()
                }),
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

        self.store_document(&uri, version).await;

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

            self.store_document(&uri, version).await;

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

        let start_version = {
            let documents = self.documents.read().await;
            documents.get(&uri).and_then(|d| d.version)
        };

        let tokens = self
            .with_workspace_file_map(&uri, |ws: &LspWorkspace, file_id| {
                let db = &*ws.db;
                let source = db.get_input::<FileSource>(file_id);
                let query_tokens = query_semantic_tokens(db, file_id);
                semantic_tokens::encode_tokens(&query_tokens.data, source.as_str())
            })
            .await;

        // If the document version changed while we were computing, drop
        // this response to avoid stale coloring. The client will re-request.
        if start_version.is_some() {
            let current_version = {
                let documents = self.documents.read().await;
                documents.get(&uri).and_then(|d| d.version)
            };
            if current_version != start_version {
                return Ok(None);
            }
        }

        match tokens {
            Some(tokens) => Ok(Some(SemanticTokensResult::Tokens(tokens))),
            None => Ok(None),
        }
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        let locations = self
            .with_workspace_file_map(&uri, |ws: &LspWorkspace, file_id| {
                let db = &*ws.db;

                let node_id = find_at_position(
                    db,
                    file_id,
                    position.line as usize,
                    position.character as usize,
                )?;

                let targets = symbol_targets(db, node_id);
                if targets.is_empty() {
                    return None;
                }

                let resolve_location = |identity: &SymbolIdentity| -> Option<(Url, Span)> {
                    match identity {
                        SymbolIdentity::Def(def_target) => {
                            let record = definition_record(db, def_target.clone())?;
                            match record.source_location? {
                                SourceLocation::Workspace { file, span } => {
                                    let metadata = db.get_input::<FileMetadata>(file);
                                    let uri = filepath_to_uri(&metadata.path)?;
                                    Some((uri, span))
                                }
                                SourceLocation::Library { filepath, span } => {
                                    let uri = filepath_to_uri(&filepath)?;
                                    Some((uri, span))
                                }
                            }
                        }
                        SymbolIdentity::Local(local_id) => {
                            let defs = local_binding_definitions(db, local_id.owner.file);
                            let def_node_id = defs.get(local_id)?;
                            let span = locations::span_of(db, *def_node_id)?;
                            let metadata = db.get_input::<FileMetadata>(local_id.owner.file);
                            let uri = filepath_to_uri(&metadata.path)?;
                            Some((uri, span))
                        }
                    }
                };

                let mut seen = HashSet::new();
                let mut locations = Vec::new();

                for target in &targets {
                    if let Some((uri, span)) = resolve_location(&target.identity) {
                        if seen.insert((uri.clone(), span)) {
                            locations.push(Location {
                                uri,
                                range: span_to_range(span),
                            });
                        }
                    }
                }

                if locations.is_empty() {
                    None
                } else {
                    Some(locations)
                }
            })
            .await
            .flatten();

        match locations {
            Some(locs) => Ok(Some(GotoDefinitionResponse::Array(locs))),
            None => Ok(None),
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        let items = self
            .with_workspace_file_map(&uri, |ws: &LspWorkspace, file_id| {
                let db = &*ws.db;
                let source = db.get_input::<FileSource>(file_id);
                let pos = lsp_position_to_pos(source.as_str(), &position);

                let ctx = completion_context(db, file_id, pos)?;

                let mut items: Vec<CompletionItem> = Vec::new();

                match &ctx.kind {
                    CompletionKind::Member => {
                        let receiver_ty = ctx.receiver_type.as_ref()?;
                        for (name, def_target) in methods_for_type(db, receiver_ty.clone()) {
                            let detail = display_def_type(db, &def_target);
                            items.push(CompletionItem {
                                label: name,
                                kind: Some(CompletionItemKind::METHOD),
                                detail,
                                ..CompletionItem::default()
                            });
                        }
                    }
                    CompletionKind::Scope => {
                        for (name, entry) in &ctx.scope {
                            let (kind, detail) = scope_entry_info(db, entry);
                            items.push(CompletionItem {
                                label: name.clone(),
                                kind: Some(kind),
                                detail,
                                ..CompletionItem::default()
                            });
                        }
                    }
                    CompletionKind::ModuleMember(module_path) => {
                        let exports = module_def_index(db, module_path.clone());
                        for (name, result) in &exports {
                            let Some(item) = result.as_ref().ok() else {
                                continue;
                            };
                            let (kind, detail) = exported_item_info(db, item);
                            items.push(CompletionItem {
                                label: name.clone(),
                                kind: Some(kind),
                                detail,
                                ..CompletionItem::default()
                            });
                        }
                    }
                    CompletionKind::TypeMember(def_target) => {
                        for (name, item_target) in associated_items(db, def_target.clone()) {
                            let detail = display_def_type(db, &item_target);
                            items.push(CompletionItem {
                                label: name,
                                kind: Some(CompletionItemKind::FUNCTION),
                                detail,
                                ..CompletionItem::default()
                            });
                        }
                    }
                }

                // Rank by type compatibility if expected_type is known
                if let Some(ref expected) = ctx.expected_type {
                    rank_by_type_compatibility(&mut items, expected);
                }

                Some(items)
            })
            .await
            .flatten();

        match items {
            Some(items) => Ok(Some(CompletionResponse::Array(items))),
            None => Ok(None),
        }
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

impl RayLanguageServer {
    pub(crate) fn new(client: Client) -> Self {
        RayLanguageServer {
            client,
            documents: RwLock::new(HashMap::new()),
            diagnostics_published_version: RwLock::new(HashMap::new()),
            workspace_root: RwLock::new(None),
            toolchain_root: RwLock::new(None),
            workspace_manager: RwLock::new(WorkspaceManager::new()),
            semantic_refresh_pending: Arc::new(AtomicBool::new(false)),
            semantic_compute: Arc::new(Semaphore::new(1)),
        }
    }

    async fn schedule_semantic_tokens_refresh(&self) {
        // Debounce: schedule at most one refresh every ~100ms
        let acquired = self
            .semantic_refresh_pending
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok();
        if acquired {
            let client = self.client.clone();
            let flag = Arc::clone(&self.semantic_refresh_pending);
            tokio::spawn(async move {
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
    async fn store_document(&self, uri: &Url, version: Option<i32>) {
        self.documents
            .write()
            .await
            .insert(uri.clone(), DocumentData::new(version));
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
    }

    async fn publish_diagnostics(&self, uri: &Url) {
        let version = {
            let documents = self.documents.read().await;
            match documents.get(uri) {
                Some(document) => document.version,
                None => {
                    let _ = self
                        .client
                        .publish_diagnostics(uri.clone(), Vec::new(), None)
                        .await;
                    return;
                }
            }
        };

        // Skip duplicate publishes for the same version to avoid flicker.
        {
            let last = self.diagnostics_published_version.read().await;
            if let Some(prev) = last.get(uri) {
                if *prev == version {
                    return;
                }
            }
        }

        // Use the incremental query system to collect diagnostics.
        let raw_diagnostics = self
            .with_workspace_file_map(uri, |ws: &LspWorkspace, file_id| {
                let db = &*ws.db;
                let errors = file_diagnostics(db, file_id);
                let metadata = db.get_input::<FileMetadata>(file_id);
                log::info!(
                    "[diagnostics] file_id={:?} path={} errors={} srcs={}",
                    file_id,
                    metadata.path,
                    errors.len(),
                    errors.iter().map(|e| e.src.len()).sum::<usize>(),
                );
                for (i, err) in errors.iter().enumerate() {
                    let paths: Vec<_> = err.src.iter().map(|s| s.filepath.to_string()).collect();
                    log::info!(
                        "[diagnostics]   error[{}]: {:?} msg={:?} src_paths={:?}",
                        i,
                        err.kind,
                        err.msg,
                        paths,
                    );
                }
                diagnostics::map_errors(errors, &metadata.path)
            })
            .await;

        let (found, raw_diagnostics) = match raw_diagnostics {
            Some(diags) => (true, diags),
            None => (false, Vec::new()),
        };

        if !found {
            log::warn!(
                "[diagnostics] with_workspace_file_map returned None for {}",
                uri
            );
        }

        let deduped = diagnostics::dedup_diagnostics(raw_diagnostics);
        log::info!(
            "[diagnostics] publishing {} diagnostics for {} (version={:?})",
            deduped.len(),
            uri,
            version,
        );

        let _ = self
            .client
            .publish_diagnostics(uri.clone(), deduped, version)
            .await;

        {
            let mut last = self.diagnostics_published_version.write().await;
            last.insert(uri.clone(), version);
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

/// Get the display type string for a definition target.
///
/// Uses `display_ty` to map internal type variables to user-facing names.
/// For workspace definitions, uses the definition's own DefId as the owner.
fn display_def_type(db: &Database, target: &DefTarget) -> Option<String> {
    let scheme = def_scheme(db, target.clone())?;
    match target {
        DefTarget::Workspace(def_id) => {
            let displayed = display_ty(db, *def_id, &scheme.ty);
            Some(displayed.to_string())
        }
        DefTarget::Library(lib_def_id) => {
            let displayed = display_library_ty(db, lib_def_id, &scheme.ty);
            Some(displayed.to_string())
        }
        DefTarget::Primitive(_) => Some(scheme.ty.to_string()),
    }
}

/// Get the LSP `CompletionItemKind` and optional detail string for a scope entry.
fn scope_entry_info(db: &Database, entry: &ScopeEntry) -> (CompletionItemKind, Option<String>) {
    match entry {
        ScopeEntry::Local(local_id) => {
            let detail = local_binding_names(db, local_id.owner.file)
                .get(local_id)
                .and_then(|_name| {
                    let defs = local_binding_definitions(db, local_id.owner.file);
                    let node_id = defs.get(local_id)?;
                    let ty = ty_of(db, *node_id)?;
                    let displayed = display_ty(db, local_id.owner, &ty);
                    Some(displayed.to_string())
                });
            (CompletionItemKind::VARIABLE, detail)
        }
        ScopeEntry::Def(def_target) => {
            let kind = def_target_to_completion_kind(db, def_target);
            let detail = display_def_type(db, def_target);
            (kind, detail)
        }
        ScopeEntry::Module(_) => (CompletionItemKind::MODULE, None),
    }
}

/// Map a `DefTarget` to an LSP `CompletionItemKind` by looking up its `DefKind`.
fn def_target_to_completion_kind(db: &Database, target: &DefTarget) -> CompletionItemKind {
    match target {
        DefTarget::Workspace(def_id) => {
            let Some(header) = def_header(db, *def_id) else {
                return CompletionItemKind::VALUE;
            };
            def_kind_to_completion_kind(&header.kind)
        }
        DefTarget::Library(_) => {
            let Some(record) = definition_record(db, target.clone()) else {
                return CompletionItemKind::VALUE;
            };
            def_kind_to_completion_kind(&record.kind)
        }
        DefTarget::Primitive(_) => CompletionItemKind::KEYWORD,
    }
}

/// Map a `DefKind` to an LSP `CompletionItemKind`.
fn def_kind_to_completion_kind(kind: &DefKind) -> CompletionItemKind {
    match kind {
        DefKind::Function { .. } => CompletionItemKind::FUNCTION,
        DefKind::Struct => CompletionItemKind::STRUCT,
        DefKind::Trait => CompletionItemKind::INTERFACE,
        DefKind::TypeAlias => CompletionItemKind::TYPE_PARAMETER,
        DefKind::Method => CompletionItemKind::METHOD,
        DefKind::Binding { .. } | DefKind::AssociatedConst { .. } => CompletionItemKind::VARIABLE,
        _ => CompletionItemKind::VALUE,
    }
}

/// Get the LSP `CompletionItemKind` and optional detail string for a module export.
fn exported_item_info(db: &Database, item: &ExportedItem) -> (CompletionItemKind, Option<String>) {
    match item {
        ExportedItem::Def(def_id) => {
            let target = DefTarget::Workspace(*def_id);
            let kind = def_target_to_completion_kind(db, &target);
            let detail = display_def_type(db, &target);
            (kind, detail)
        }
        ExportedItem::Local(_) => (CompletionItemKind::VARIABLE, None),
    }
}

/// Rank completion items by type compatibility with the expected type.
///
/// Items whose detail matches the expected type sort first (sort_text = "0"),
/// items with a compatible shape sort next ("1"), and everything else sorts
/// last ("2"). Within each tier, the original order is preserved.
fn rank_by_type_compatibility(items: &mut [CompletionItem], expected: &Ty) {
    let expected_str = expected.to_string();

    for item in items.iter_mut() {
        let rank = match &item.detail {
            Some(detail) if *detail == expected_str => "0",
            Some(detail) if types_share_base(detail, &expected_str) => "1",
            _ => "2",
        };
        item.sort_text = Some(format!("{}{}", rank, item.label));
    }
}

/// Check if two type strings share the same base type name.
///
/// This is a simple heuristic: it strips generic parameters and compares
/// the base name. For example, `List[int]` and `List[string]` share base
/// `List`.
fn types_share_base(a: &str, b: &str) -> bool {
    let base_a = a.split('[').next().unwrap_or(a).trim();
    let base_b = b.split('[').next().unwrap_or(b).trim();
    !base_a.is_empty() && base_a == base_b
}
