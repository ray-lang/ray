# Incremental Compiler Frontend

## 1. Summary & Goals

This document describes the design for Ray's incremental compiler frontend, replacing the current monolithic pipeline with a query-based architecture. The current system merges all files into a single module and reprocesses everything on each change, making LSP interactions slow and CLI rebuilds inefficient. The new system preserves file boundaries, caches intermediate results, and invalidates only what's necessary when sources change.

### A. Goals

- **LSP responsiveness**: Sub-second feedback on edits, even in multi-file modules. Typing in one file should not require re-typechecking unrelated files.
- **CLI build caching**: Incremental rebuilds that skip unchanged work. Editing a function body should not re-typecheck the entire module.
- **Correctness**: Cross-file binding groups must typecheck correctly. The new system must produce identical results to the current system for valid programs.
- **Maintainability**: Clear separation between stages. Each query is a pure function from inputs to outputs, making the system easier to test and reason about.
- **Graceful degradation**: Errors in one file should not block analysis of other files. Partial results are always available.

### B. Non-Goals (for this design)

- **Parallelism**: Single-threaded execution is sufficient. The design should not preclude future parallelization, but it is not a goal.
- **Per-expression granularity**: The system operates at definition granularity (DefId) for typechecking. Finer granularity (caching within a function body) is not a goal.
- **Codegen**: LIR generation and LLVM codegen are out of scope. The system ends at typechecking, but outputs must be consumable by downstream codegen.

### C. Success Criteria

- Editing a function body in an annotated function does not re-typecheck other files
- LSP hover/completion responds in under 200ms for typical edits
- Full rebuild of the core library matches current system output exactly
- Each query is independently testable with mock inputs

## 2. Current Frontend (Legacy)

The current frontend is orchestrated by `Driver::build_frontend()` in `ray-driver`. It operates on entire modules at once, merging all files into a single `Module<(), Decl>` before running analysis passes. This section documents each stage, its current implementation, and barriers to incrementality.

### A. Stages

#### I. Parsing

**Entry point**: `Parser::parse_from_src()` in `ray-core/src/parse/parser/mod.rs`

**What it does**: Lexes and parses a single file into an AST (`ast::File`), populating a `SourceMap` with span information for each node.

**Inputs**: Source text, file path, module path
**Outputs**: `ast::File` (containing imports, declarations, top-level statements), `SourceMap`, parse errors

**Current state**: Already per-file and mostly pure. The parser allocates `NodeId`s via a global counter, which could interfere with caching if not managed carefully.

**Incrementality notes**: This stage is a good candidate for direct queryification. The main challenge is `NodeId` stability across edits.

#### II. Import & Module Resolution

**Entry point**: `ModuleBuilder::build()` in `ray-core/src/sema/modules.rs`

**What it does**: Starting from an entry file, discovers all files in a module (sibling files in directory modules), resolves import statements to file paths or `.raylib` libraries, and recursively builds dependencies.

**Inputs**: Entry file path, file system, overlays (in-memory edits), `RayPaths` configuration
**Outputs**: `HashMap<Path, Module<Expr, Decl>>` (one per file/submodule), `HashMap<Path, SourceMap>`, loaded `RayLib` artifacts

**Current state**: Deeply impure. Reads from file system, manages global `NameContext`, tracks which modules have been built to avoid cycles. Interleaves parsing with import resolution.

**Incrementality notes**: Must be split into:
1. Module discovery (which files exist, module structure)
2. Import resolution (which modules does each file import)
3. Dependency loading (loading `.raylib` files)

#### III. Name Resolution

**Entry point**: `Module::resolve_names()` called from `ModuleCombiner::combine()` in `ray-core/src/transform/mod.rs`

**What it does**: Resolves unqualified names to fully-qualified paths using import scopes. Each file has its own import scope, but sibling files in a module can reference each other's definitions without imports.

**Inputs**: Parsed module, `NameContext`, scope map (imports per file)
**Outputs**: Mutated AST with resolved paths, updated `NameContext`

**Current state**: Operates on the merged module after all files are combined. Mutates the AST in place. Uses `NameContext` which accumulates state across files.

**Incrementality notes**: Must be reworked to:
1. Compute per-file exports (what names does this file define)
2. Compute per-file imports (what names does this file need from elsewhere)
3. Resolve names per-file using exports from siblings and imported modules

#### IV. AST Lowering/Desugaring

**Entry point**: `Decl::lower()` called from `ModuleCombiner::combine()` in `ray-core/src/transform/mod.rs`

**What it does**: Transforms the AST from `Module<Expr, Decl>` to `Module<(), Decl>`. Resolves type annotations to `Ty` values, registers structs/traits/impls in `GlobalEnv`, populates operator tables.

**Inputs**: Name-resolved AST, `TyCtx`, `NameContext`, `SourceMap`
**Outputs**: Lowered AST, populated `GlobalEnv` (via `TyCtx`), type annotations resolved

**Current state**: Mutates `TyCtx.global_env` to register nominal types. Operates on the merged module. The `AstLowerCtx` carries mutable references to multiple global structures.

**Incrementality notes**: Can be split into:
1. Per-file nominal type collection (structs, traits declared in this file)
2. Global `GlobalEnv` construction (merging nominal types from all files)
3. Per-file AST lowering (using the global `GlobalEnv` for type resolution)

#### V. Binding Analysis

**Entry point**: `run_binding_pass()` in `ray-core/src/passes/binding.rs`

**What it does**: Walks the merged AST and builds a `BindingGraph` that tracks:
- All value bindings (functions, let-bindings, parameters)
- Dependencies between bindings (which bindings reference which others)
- Mapping from `NodeId` to `BindingId`
- Mapping from `Path` to `BindingId`

**Inputs**: Merged `Module<(), Decl>`, `SourceMap`, `GlobalEnv`, seed bindings from libraries
**Outputs**: `BindingPassOutput` containing `BindingGraph`, `BindingRecord`s, node/path mappings

**Current state**: Operates on the merged module. The pass itself is relatively pure (reads AST, produces output), but assumes all files have been combined.

**Incrementality notes**: The binding graph must span files (for cross-file binding groups), but per-file binding information can be computed independently. The challenge is:
1. Compute per-file bindings and references
2. Merge into a cross-file binding graph
3. Compute SCCs (binding groups) from the merged graph

#### VI. Closure Analysis

**Entry point**: `run_closure_pass()` in `ray-core/src/passes/closure.rs`

**What it does**: Identifies closure expressions and determines their capture sets (which bindings from enclosing scopes are referenced inside the closure).

**Inputs**: Merged `Module<(), Decl>`, `SourceMap`, `BindingPassOutput`
**Outputs**: `ClosurePassOutput` containing `ClosureInfo` for each closure

**Current state**: Pure function of its inputs. Operates on merged module but doesn't require cross-file information beyond what's in `BindingPassOutput`.

**Incrementality notes**: This pass is already close to pure. With per-file binding information, closure analysis can run per-file. Closures cannot capture across file boundaries (only module-level bindings, which are not "captured" in the closure sense).

#### VII. Typing IR Lowering

**Entry point**: `lower_module()` in `ray-core/src/typing.rs`

**What it does**: Converts the AST representation into the type system's IR (`ModuleInput`). Creates `ExprRecord` and `PatternRecord` maps that the type checker uses instead of traversing the AST directly.

**Inputs**: Merged `Module<(), Decl>`, `SourceMap`, `GlobalEnv`, `BindingPassOutput`, schema allocator
**Outputs**: `ModuleInput` containing expression/pattern records, binding graph, binding records

**Current state**: Pure transformation. Clones data from `BindingPassOutput` and builds the type system's view of the module.

**Incrementality notes**: Can be done per-file once binding analysis produces per-file outputs. The `ModuleInput` for a file only needs that file's expressions/patterns plus the global binding graph for resolving cross-file references.

#### VIII. Typechecking

**Entry point**: `check_module()` in `ray-typing/src/lib.rs`

**What it does**:
1. Computes binding groups (SCCs of mutually-dependent bindings)
2. For each group in topological order: generates constraints, solves them, generalizes types
3. Stores inferred type schemes in `TyCtx`

**Inputs**: `ModuleInput`, `TypecheckOptions`, `TyCtx`, `NameContext`
**Outputs**: `TypeCheckResult` containing type errors, with schemes stored in `TyCtx`

**Current state**: The typechecker itself is relatively pure given its inputs, but it mutates `TyCtx` to store results. Binding groups can span files, so typechecking cannot be trivially parallelized by file.

**Incrementality notes**: The natural caching unit is the **binding group**, not the file. Key insight:
- Annotated functions have syntactically-known signatures; body changes don't affect dependents
- Unannotated functions have inferred signatures; body changes may propagate through the binding group
- Binding groups can span files, so invalidation must track cross-file dependencies

### B. Reuse

The following components can be preserved with refactoring. See Section 5 (Legacy System Audit) for detailed modification requirements for each component.

**Preserve as-is or with minor changes:**
- **Parser** (`ray-core/src/parse`): Already per-file. Needs stable `NodeId` allocation strategy.
- **Closure pass** (`ray-core/src/passes/closure.rs`): Already pure, just needs per-file inputs.
- **Type checker core** (`ray-typing`): The constraint generation, solving, and generalization logic is sound. Needs to accept per-group inputs rather than whole-module inputs.

**Preserve logic, restructure interface:**
- **Binding pass** (`ray-core/src/passes/binding.rs`): The binding graph construction logic is correct. Needs to work per-file and then merge results.
- **Typing IR lowering** (`ray-core/src/typing.rs`): Pure transformation that can work per-file.

**Requires significant rework:**
- **Module builder** (`ray-core/src/sema/modules.rs`): The file discovery and import resolution logic is intertwined with parsing and global state. Must be decomposed into separate queries.
- **Name resolution** (`ray-core/src/sema/resolve.rs`, `ray-core/src/transform/mod.rs`): Currently operates on merged module. Must be reworked for per-file operation with cross-file export/import tracking.
- **AST lowering** (`ray-core/src/transform/mod.rs`): Combines files and lowers in one pass. Must separate file combination from lowering, and make lowering per-file.

**Must be replaced:**
- **`ModuleCombiner`** (`ray-core/src/transform/mod.rs`): The entire "combine all files then process" approach is incompatible with incrementality. The concept of a merged module should not exist in the new system.

## 3. Query-based Frontend

### A. Overview

The new frontend models compilation as a directed graph of **queries**. Each query is a pure function: given its inputs, it deterministically produces outputs. The query engine (building on the existing infrastructure in `ray-frontend/src/query.rs`) memoizes results and tracks which queries depend on which inputs. When an input changes, only queries that transitively depend on that input are recomputed.

#### Inputs vs Queries

The system distinguishes between two kinds of nodes in the dependency graph:

- **Inputs**: External data provided to the system. These are the "leaves" of the dependency graph - they have no dependencies themselves, only dependents. Examples: file contents, file system structure, overlay edits from LSP, precompiled `.raylib` data.

- **Queries**: Computed values derived from inputs or other queries. Each query declares its key type (what identifies a particular invocation) and value type (what it produces). Examples: `parse(file)`, `exports(file)`, `typecheck(binding_group)`.

#### Granularity

The system operates at two levels of granularity:

1. **File granularity** for early pipeline stages: parsing, module discovery, import resolution. These queries are keyed by `FileId` and can run independently per file.

2. **Definition granularity** for later stages: binding analysis, typechecking. These queries are keyed by `DefId` (a top-level definition) or `BindingGroup` (a set of mutually-recursive definitions).

Typechecking specifically operates at **binding group** granularity because:

1. Binding groups (SCCs of mutually-recursive definitions) are the natural unit of type inference
2. Binding groups can span multiple files
3. Caching at the binding group level allows body changes in annotated functions to avoid re-typechecking dependents

This is not "file-level queries first, item-level later" - definition-level identity (`DefId`) is foundational from the start. The distinction is between *file-keyed* queries (where the key is a file) and *definition-keyed* queries (where the key is a definition within a file).

#### No Merged Module

Unlike the current system, there is no single "merged module" that combines all files. Each file's AST remains distinct throughout the pipeline. Cross-file information (like the binding graph) is computed by queries that aggregate per-file results, but the per-file data is never flattened into a single structure.

Similarly, there is no monolithic "global environment" containing all type definitions. Instead, nominal type information (structs, traits, impls) is accessed through queries keyed by `DefTarget`: `struct_def(target)`, `trait_def(target)`, `impls_for_type(target)`. When typechecking needs to know about a type, it:

1. Resolves the name to a DefTarget via `def_for_path(path)`
2. Queries the definition via `struct_def(target)` or similar

This means changing a struct definition only invalidates code that actually depends on that struct, not everything. And because DefIds are structural (not name-based), renaming a type doesn't invalidate its definition - only the name resolution queries are affected.

#### Two-Phase Structure

The query graph naturally divides into two phases:

1. **Per-file phase**: Queries keyed by `FileId` that can run independently for each file. Parse, extract exports, resolve names, lower AST, compute per-file bindings.

2. **Cross-file phase**: Queries that require information from multiple files. Merge binding graphs, compute binding groups (SCCs), typecheck each group.

The boundary between phases is where per-file results are aggregated. A change to one file invalidates its per-file queries, which may invalidate cross-file queries, which may invalidate typechecking for affected binding groups - but unrelated files and binding groups remain cached.

#### Design Invariant

**All syntax path resolution happens in file-keyed name resolution. All semantic queries consume DefIds.**

This is the key architectural boundary. The `name_resolutions(FileId)` query (and its dependencies: `resolved_imports`, `module_def_index`) is the only place where string-based path lookup occurs. Once a name is resolved to a `DefId`, all downstream queries work exclusively with DefIds. No query after name resolution ever needs to "look up a name" - it already has the DefId.

This means:
- Context (which module am I in? what's imported?) is confined to name resolution
- Semantic queries like `def_scheme(DefTarget)` never need import context
- Renaming propagates only through name resolution, not through the type system

#### Query Engine

The query system is implemented in `ray-frontend/src/query.rs` with macro support in `ray-query-macros`. It is a lightweight custom implementation (not salsa) tailored to Ray's needs.

**Core abstractions**:

- **`Input` trait**: Represents external data provided to the system. Inputs have a key type, value type, and fingerprint function. Defined via `#[input]` on structs:

  ```rust
  #[input(key = "FileId")]
  struct FileSource(String);
  ```

- **`Query` trait**: Represents computed values derived from inputs or other queries. Each query has a key type, value type, and `compute(db, key) -> value` function. Defined via `#[query]` on functions:

  ```rust
  #[query]
  fn parse(db: &Database, file_id: FileId) -> ParseResult {
      let source = db.get_input::<FileSource>(file_id);
      // ... parsing logic
  }
  ```

- **`Database`**: Holds input values and cached query results. Provides `get_input<I>(key)` and `query<Q>(key)` methods.

**Memoization**: Query results are cached in memory for the duration of a session. The cache is not persisted to disk - CLI creates a fresh `Database` per build, LSP maintains one across edits.

**Dependency tracking**: Automatic during query execution. When `compute()` runs, the system records which inputs and queries are accessed. These dependencies are stored with the cached result.

**Invalidation**: Fingerprint-based. Each input has a `fingerprint()` function (typically a hash). When a query result is requested:

1. Check if a cached result exists
2. If so, verify all recorded input fingerprints still match current values
3. If fingerprints match, return cached result
4. Otherwise, recompute and cache the new result

This is "validation on access" rather than eager invalidation - the system doesn't proactively invalidate when inputs change, it verifies validity when results are requested.

**Cycle handling**: The system detects cycles via stack inspection during execution. Each query type specifies a `CyclePolicy`:

- `CyclePolicy::Panic` (default): Panic on cycle detection
- `CyclePolicy::Error`: Call `on_cycle(db, key)` to produce a fallback value

### B. Data Structures

#### I. Path Types

The system distinguishes between two kinds of paths to avoid ambiguity:

```rust
/// A module path identifies a module in the module hierarchy.
/// Examples: `core`, `core::collections`, `myproject::utils`
///
/// Module paths correspond to directories or single-file modules.
/// They are used as keys in WorkspaceSnapshot.modules and for library lookup.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModulePath(Vec<String>);

/// An item path (FQN) identifies a specific definition within a module.
/// Examples: `core::int::add`, `myproject::utils::helper`
///
/// Item paths are used for name resolution and cross-reference lookup.
/// An item path is a module path plus an item name (and possibly nested names for impl members).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ItemPath {
    pub module: ModulePath,
    pub item: Vec<String>,  // e.g., ["List", "push"] for List::push
}
```

**Usage**:
- `ModulePath`: Keys `WorkspaceSnapshot.modules`, `LibraryData`, `binding_graph(module)`, `binding_groups(module)`
- `ItemPath`: Keys `def_for_path(item_path)`, used in name resolution results

This distinction prevents confusion between "the module `core::fmt`" and "the item `core::fmt::Display`".

**ItemPath canonicalization**: `def_for_path(ItemPath)` performs **syntactic canonicalization** only:

1. **Type arguments are stripped**: `List[int]::push` → `List::push`. Type arguments affect monomorphization, not identity.
2. **Path syntax is normalized**: Consistent separator handling, whitespace normalization, etc.

| Syntax | Canonical ItemPath |
|--------|-------------------|
| `List[int]::push` | `module::List::push` (type args stripped) |
| `Iterable::next` | `module::Iterable::next` (preserved as-is) |

**Type-directed method resolution** is NOT part of `def_for_path`. When calling `x.push()` where `x: List[int]`, determining which concrete impl method to call requires type information and happens in `call_resolution(NodeId)`, not in path lookup. See the Call Resolution queries for details.

#### II. Identity

The query system requires stable identifiers for files, definitions, and AST nodes. These identifiers serve as keys in query caches and must remain stable across edits to unrelated code. Identity is **structural** (based on origin/location) rather than **nominal** (based on names), which decouples identity from name resolution.

##### FileId

A `FileId` identifies a source file within the workspace. It is the key for file-level queries like parsing.

```rust
/// Identifies a source file in the workspace.
///
/// FileIds are assigned during workspace indexing and remain stable as long
/// as the file exists. The id is an index into the workspace's file list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);
```

**Stability**: FileIds are stable as long as the file exists. Creating or deleting other files does not change a file's FileId. Renaming a file effectively deletes the old FileId and creates a new one.

**Usage**: FileIds appear in:
- Query keys for file-level queries (`parse(file_id)`, `file_exports(file_id)`)
- DefId (as the origin of a definition)
- Error messages and diagnostics

##### DefId

A `DefId` identifies a definition that can be referenced from outside its containing scope. DefIds are **structural** - they encode where the definition lives, not what it's named.

**What gets a DefId** (the "definition model"):

| Kind | Gets DefId? | Notes |
|------|-------------|-------|
| Functions (top-level) | Yes | Including `fn main()` |
| Functions (in impl) | Yes | Each method is a separate DefId |
| Functions (in trait) | Yes | Trait method signatures get DefIds |
| Structs | Yes | |
| Traits | Yes | |
| Impl blocks | Yes | The impl as a whole gets a DefId |
| Type aliases | Yes | |
| Constants (top-level) | Yes | |
| Nested functions | **No** | Closures get `LocalBindingId`, not DefId |
| Parameters | **No** | Get `LocalBindingId` |
| Let-bindings | **No** | Get `LocalBindingId` |

**Note on trait methods**: Default trait method bodies are not currently supported in Ray. Trait definitions contain only method signatures, not implementations. This means trait method DefIds have no body to typecheck - they only contribute a type signature to the system.

**Parsing produces all DefIds**: The `parse` query produces a flat list of all DefIds in a file (in `ParseResult.defs`), including methods inside impl blocks and trait definitions. This is **not** just syntactic top-level items - it includes all items that can be referenced cross-definition.

**Parent relationship**: For impl/trait members, the DefId encodes the parent relationship:

```rust
pub struct DefId {
    pub file: FileId,
    pub local_index: u32,
}

// The parent of a method is tracked separately:
pub fn def_parent(DefId) -> Option<DefId>;  // Returns impl/trait DefId for methods
```

**Why this boundary**: DefIds mark the unit of cross-definition dependency tracking. Nested functions (closures) cannot be referenced from outside their containing function, so they don't need cross-file identity. They're part of their containing definition's body.

```rust
/// Identifies a top-level definition in the program.
///
/// DefIds are structural: they identify a definition by its location (file +
/// index within file), not by its name. This makes them stable across renames
/// and decouples identity from name resolution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DefId {
    /// The file containing this definition.
    pub file: FileId,
    /// Index of this definition within the file (in source order).
    pub local_index: u32,
}
```

**File-main DefId**: Each file has a reserved `DefId { file, local_index: 0 }` representing its top-level execution context. This "file-main" owns all top-level statements that aren't definitions themselves (e.g., expression statements like `foo(a)`). Top-level constants, variables, functions, etc. get `local_index: 1..`. The file-main DefId:
- Is unannotated (must be typed together with referenced unannotated definitions)
- Cannot be referenced cross-module (it's not exported)
- Creates inference edges to unannotated definitions it references
- NodeIds for top-level expression statements have `owner: DefId { file, local_index: 0 }`

This keeps the execution model abstract - no actual "main function" is created until codegen - while ensuring all top-level statements in a file share a typing context.

**Stability**: DefIds are stable across:
- Edits to the definition's body
- Edits to bodies of other definitions in the same file
- Edits to other files
- Renames (the DefId stays the same; only the name lookup changes)

DefIds change when:
- The definition is deleted
- A new definition is inserted before it in the same file (shifts indices)
- The file is deleted or renamed

**Stability tradeoff**: Position-based indexing means inserting a definition at the top of a file shifts all subsequent DefIds, invalidating their cached results. This is a deliberate simplicity-first choice:

- **What we optimize for**: Body edits (the common case) - editing a function body never changes any DefId
- **What we accept churn on**: Top-of-file insertions - rare in practice, and the invalidation is bounded to one file's definitions
- **Future option**: Anchor-based DefIds (e.g., hash of signature) could make insertion stable, but adds complexity

For the initial implementation, position-based indexing provides a good tradeoff between simplicity and cache effectiveness.

**Usage**: DefIds appear in:
- The binding graph (edges connect DefIds)
- Query keys for definition-level queries (`scheme_of(def_id)`, `closure_info(def_id)`)
- LocalBindingId and NodeId (as the owner)

**Path lookup**: To find a definition by name, use `def_for_path(ItemPath) -> Option<DefTarget>`. This is a derived query, not the primary identity. This separation means:
- Renaming a definition doesn't invalidate its DefId or cached type information
- Two definitions with the same name (in different files) have different DefIds
- Name resolution errors don't prevent the rest of the system from functioning

##### LocalBindingId

A `LocalBindingId` identifies a binding local to a definition: a parameter, let-binding, match binding, or for-loop variable. Local bindings exist within the scope of a single DefId and never participate in cross-definition dependencies.

```rust
/// Identifies a local binding within a top-level definition.
///
/// Local bindings are scoped to their owning definition and are not visible
/// outside it. They do not participate in the binding graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalBindingId {
    /// The definition containing this binding.
    pub owner: DefId,
    /// A sequential index assigned during AST traversal of the owner.
    pub index: u32,
}
```

**Stability**: LocalBindingIds are stable within their owning definition. The index is assigned by a deterministic traversal of the definition's AST. Edits to other definitions do not affect a definition's local binding indices.

**Usage**: LocalBindingIds appear in:
- Local symbol tables during typechecking
- Closure capture sets (which locals are captured)
- Error messages referencing local variables

**Important**: LocalBindingIds never appear in the binding graph. The binding graph only tracks dependencies between top-level definitions (DefIds).

##### NodeId

A `NodeId` identifies an AST node within a definition: an expression, pattern, type annotation, or statement. NodeIds are used to attach metadata (spans, types, diagnostics) to specific syntactic locations.

```rust
/// Identifies an AST node within a top-level definition.
///
/// NodeIds are used to map between AST nodes and their associated metadata
/// (source spans, inferred types, diagnostics).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId {
    /// The definition containing this node.
    pub owner: DefId,
    /// A sequential index assigned during indexing of the owner.
    pub index: u32,
}
```

**Assignment timing**: DefIds and NodeIds are assigned during **parsing**. The parser recognizes when it enters a top-level definition and assigns a DefId at that point. NodeIds are assigned to AST nodes as they are created, scoped to the current definition.

This means:
- Parsing produces a fully-identified AST - no separate ID assignment pass needed
- All definition metadata and span mappings are collected during parsing (no separate indexing pass)
- Body edits within a definition do not affect NodeIds in other definitions
- NodeId stability is conditional on DefId stability: if a definition's DefId shifts (e.g., due to inserting a new definition before it), all NodeIds owned by that definition also shift

**Usage**: NodeIds appear in:
- SourceMap entries (mapping NodeId to Span)
- Type tables (mapping NodeId to inferred type)
- Diagnostic attachments (which node caused an error)

##### The Binding Graph

The binding graph tracks dependencies between top-level definitions. It is the foundation for computing binding groups (SCCs) and determining what needs to be re-typechecked when code changes.

**Important**: All definitions go through type inference. There are no exceptions. The binding graph determines which definitions must be inferred *together* (in the same SCC), not which definitions "skip" inference.

```rust
/// Dependency graph between top-level definitions.
///
/// The binding graph contains edges A → B when A references B and B is
/// unannotated. Edges to annotated definitions are omitted because the
/// callee's type is already known - there's no need to infer it together
/// with the caller.
///
/// Every definition in the module has an entry in `edges`, even if its
/// HashSet is empty. An annotated function that only references other
/// annotated functions has an empty edge set, making it a singleton SCC.
pub struct BindingGraph {
    /// Forward edges: definition -> unannotated definitions it references.
    /// Every DefId in the module appears as a key; the value may be empty.
    pub edges: HashMap<DefId, HashSet<DefId>>,
}
```

**Annotated vs unannotated**: A function is "annotated" if all parameter types are explicit AND either the return type is explicit or the body is an arrow expression (`=>`). See `SignatureStatus` in the `parse` query for details.

| Kind | Annotated? | Notes |
|------|------------|-------|
| Function with full signature | Yes | e.g., `fn foo(x: int) -> int { ... }` |
| Function with arrow body | Yes | e.g., `fn foo(x: int) => x + 1` (return type inferred from body) |
| Function with missing annotations | **No** | e.g., `fn foo(x) { ... }` or `fn foo(x: int) { ... }` (missing return type) |
| Methods (impl/trait) | Yes | Must have explicit signatures |
| Structs/Traits/TypeAliases | Yes | Define types, signatures are inherent |
| Constants | Depends | Annotated if type is explicit, e.g., `x: int = 1` |
| External/library definitions | Yes | Scheme from `LibraryData` |
| File-level statements | Depends | Same rules as constants |

**Edge rules**: An edge A → B is added to the binding graph when:
1. A syntactically references B (calls it, uses it as a value, etc.)
2. B is **unannotated**

If B is annotated, no edge is added - A can use B's known signature without needing to infer B's type together with A.

**SCC computation**: Binding groups are the strongly connected components of this graph. The edge rules mean:

- If annotated `fn foo() -> int` calls unannotated `fn bar()`, there **is** an edge foo → bar, so they are in the same SCC
- If annotated `fn foo() -> int` calls annotated `fn baz() -> int`, there is **no** edge, so they are in separate SCCs
- An annotated function that only references other annotated functions has no outgoing edges and becomes a singleton SCC

**Why this matters for caching**: When you edit an annotated function's body:
- Its SCC is re-typechecked
- But if it only calls other annotated functions, it's a singleton SCC
- And its callers (which had no edge to it) don't need to re-typecheck

When you edit an unannotated function's body:
- Its SCC is re-typechecked
- All callers that had edges to it are in the same SCC, so they re-typecheck too

This is why annotations improve incrementality: they break the inference coupling between caller and callee.

```rust
/// Identifier for a binding group within a module.
///
/// Using a compact ID rather than Vec<DefId> as the query key ensures that:
/// - The key is hashable and cheap to compare
/// - The query system can efficiently track dependencies
///
/// Note: BindingGroupId is stable within a given `binding_groups(module)` result,
/// but the index may change if the binding graph changes (e.g., due to edits
/// that add/remove definitions or change dependencies).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BindingGroupId {
    pub module: ModulePath,
    pub index: u32,  // SCC index in topological order
}

/// A set of mutually-recursive definitions that must be typechecked together.
///
/// Binding groups are the SCCs of the binding graph. Within a group,
/// definitions may reference each other, so their types must be inferred
/// simultaneously.
pub struct BindingGroup {
    pub id: BindingGroupId,
    pub members: Vec<DefId>,
}
```

**Module boundary rule**: Binding groups never cross module boundaries. The binding graph is computed per-module, and SCCs are found within that module's graph only. Cross-module references are treated as references to definitions with known schemes (at name resolution time):

- References to definitions in **other source modules** must have a known scheme (explicit annotation)
- References to definitions in **precompiled libraries** have known schemes (from `LibraryData`)

This means:
- `binding_graph(ModulePath)` returns edges only between DefIds in that module
- `binding_groups(ModulePath)` returns SCCs computed from that module's graph
- Cross-module edges are not part of the SCC computation; they're resolved to known schemes during typechecking

**Module import cycle handling**: Import cycles are permitted. Cross-module function calls require the callee to have a known scheme (at name resolution time) - meaning an explicit type annotation. Functions without annotations can only be called from within their defining module. This ensures each module's type inference is self-contained - no cross-module inference occurs.

This rule applies regardless of whether there's a cycle:
- Module A imports B: A can only call functions in B that have known schemes
- Module A and B import each other: same rule, both directions

The benefit is simplicity: there's no special "cycle detection" or "compilation unit merging" logic. Modules are always typechecked independently, using only the known schemes of their dependencies.

**Error handling**: When code in module A references a function `foo` in module B that lacks a known scheme (no explicit annotation), this is a name resolution error (not a type error). The `name_resolutions` query produces `Resolution::Error` for that reference, and a diagnostic is emitted:

> Cannot reference function `foo` from module `B`: no known type scheme. Add type annotations to make it callable from other modules.

This error is reported during name resolution, before typechecking begins. The call site in module A will have `Resolution::Error`, allowing typechecking to proceed with an error type rather than blocking entirely.

Local bindings do not appear in the binding graph because they cannot be referenced from outside their owning definition. A closure that captures a local variable creates a dependency on the enclosing definition, not on the local variable itself.

### C. Architecture

#### I. Inputs

Inputs are the leaves of the dependency graph - external data provided to the query system. They have no dependencies themselves, only dependents. When an input changes, the query system invalidates all cached queries that transitively depend on it.

##### WorkspaceSnapshot (The Universe)

The `WorkspaceSnapshot` is the **root input** that defines "what exists" in the compilation universe. All module discovery and file resolution flows from this single authoritative source. This avoids the "how do we know all inputs" problem - the universe is an explicit input, not an emergent property discovered ad-hoc.

```rust
/// The root input defining the compilation universe.
///
/// Contains all information needed to answer "what files and modules exist"
/// without additional filesystem access during query evaluation.
#[input]
struct WorkspaceSnapshot {
    /// Entry point file for this compilation.
    pub entry: FilePath,

    /// All known source files, indexed by FileId.
    /// FileId(n) corresponds to files[n].
    pub files: Vec<FileEntry>,

    /// Mapping from FilePath to FileId for quick lookup.
    pub path_to_id: HashMap<FilePath, FileId>,

    /// Module structure: which files belong to which module path.
    /// Derived from directory structure and file locations.
    pub modules: HashMap<ModulePath, ModuleEntry>,

    /// Search paths for resolving imports (e.g., library directories).
    pub search_paths: Vec<FilePath>,

    /// Available precompiled libraries.
    pub libraries: HashMap<ModulePath, FilePath>,
}

struct FileEntry {
    pub path: FilePath,
    pub module: ModulePath,
}

struct ModuleEntry {
    /// Files that are part of this module (siblings in a directory module).
    pub files: Vec<FileId>,
    /// Whether this module has a precompiled .raylib available.
    pub has_library: bool,
}
```

**Construction**:

The snapshot is built before query evaluation begins. Construction requires parsing imports to discover dependencies, but this is a lightweight "discovery parse" separate from the full query-based parse.

```rust
fn build_snapshot(entry: FilePath, search_paths: Vec<FilePath>) -> WorkspaceSnapshot {
    let mut snapshot = WorkspaceSnapshot::new(entry, search_paths);
    let mut pending: VecDeque<FilePath> = VecDeque::new();
    let mut seen: HashSet<FilePath> = HashSet::new();

    // Start with entry file and its module siblings
    let entry_module = discover_module_for_file(&entry);
    for file in discover_sibling_files(&entry, &entry_module) {
        pending.push_back(file);
    }

    while let Some(path) = pending.pop_front() {
        if !seen.insert(path.clone()) { continue; }

        // Add file to snapshot
        let file_id = snapshot.add_file(path.clone());
        let module = discover_module_for_file(&path);
        snapshot.add_to_module(module.clone(), file_id);

        // Lightweight parse to extract imports (not full AST)
        let source = std::fs::read_to_string(&path)?;
        let imports = extract_imports(&source);

        for import_path in imports {
            match resolve_import(&import_path, &module, &snapshot.search_paths) {
                ImportResolution::SourceModule(module_path, files) => {
                    // Source module: add all its files to pending
                    for file in files {
                        pending.push_back(file);
                    }
                }
                ImportResolution::Library(module_path, lib_path) => {
                    // Precompiled library: record it, don't traverse
                    snapshot.add_library(module_path, lib_path);
                }
                ImportResolution::NotFound => {
                    // Will be reported as error during name resolution
                }
            }
        }
    }

    snapshot
}
```

**Created by**:
- **CLI**: Calls `build_snapshot` starting from the entry file. This happens once at startup.
- **LSP**: Starts with the same construction, then incrementally updates the snapshot when the file watcher reports changes (file creation, deletion, rename).

**What it answers**:
- `file_id(FilePath) -> Option<FileId>` - Does this file exist? What's its ID?
- `file_path(FileId) -> FilePath` - What's the path for this ID?
- `module_for_file(FileId) -> ModulePath` - What module does this file belong to?
- `files_in_module(ModulePath) -> Vec<FileId>` - What files are in this module?
- `library_for_module(ModulePath) -> Option<FilePath>` - Is there a precompiled library?

**Why a snapshot**: The snapshot is immutable during query evaluation. This means:
- Queries never touch the filesystem directly
- Results are deterministic and reproducible
- The CLI/LSP controls when the universe changes

**Fingerprinting**: The snapshot itself is fingerprinted by hashing its structure. In practice, the CLI creates a new Database for each build, and the LSP updates the snapshot incrementally (which naturally invalidates affected queries).

##### FileSource

```rust
#[input(key = "FileId")]
struct FileSource(String);
```

The source text of a file. Keyed by `FileId` (not FilePath), returns the file's contents as a `String`.

**Set by**:
- CLI: Reads from disk for each FileId in the WorkspaceSnapshot
- LSP: Sets from editor buffer on each edit; falls back to disk for unopened files

**Fingerprinting**: Hash of the string content. Setting the same content twice does not invalidate dependents.

##### LibraryData

```rust
#[input(key = "ModulePath")]
struct LibraryData {
    /// Type schemes for all exported definitions, keyed by ItemPath
    pub schemes: HashMap<ItemPath, TyScheme>,

    /// Struct definitions
    pub structs: HashMap<ItemPath, StructDef>,

    /// Trait definitions
    pub traits: HashMap<ItemPath, TraitDef>,

    /// Impl definitions
    pub impls: HashMap<ItemPath, ImplDef>,

    /// Index: type -> impls for that type (for impls_for_type query)
    pub impls_by_type: HashMap<ItemPath, Vec<ItemPath>>,

    /// Index: trait -> impls of that trait (for impls_for_trait query)
    pub impls_by_trait: HashMap<ItemPath, Vec<ItemPath>>,

    /// Operator tables (infix and prefix)
    pub operators: OperatorIndex,

    /// IDE metadata for hover/go-to-definition
    pub definitions: HashMap<ItemPath, DefinitionRecord>,

    /// Source spans for error messages pointing into library code
    pub source_map: SourceMap,

    /// Module paths contained in this library
    pub modules: Vec<ModulePath>,
}
```

Precompiled library data from a `.raylib` file. Keyed by `ModulePath`. Provides efficient lookup for queries that need library information:
- `def_scheme(DefTarget::External(path))` → `lib.schemes.get(path)`
- `struct_def(DefTarget::External(path))` → `lib.structs.get(path)`
- `impls_for_type(target)` → `lib.impls_by_type.get(type_path)`

**Schema variable remapping**: When a `.raylib` file is loaded, schema variables are remapped to avoid collisions with the workspace's `SchemaVarAllocator`. The loader:
1. Reads the library's max schema var ID from the file
2. Allocates that many fresh IDs from the global `SchemaVarAllocator`
3. Builds a substitution mapping old IDs to new IDs
4. Applies the substitution to all `TyScheme` values in the library

This ensures that `'?s0` in one library doesn't collide with `'?s0` from another library or from workspace code.

**Set by**:
- CLI: Loads `.raylib` files from paths specified in WorkspaceSnapshot.libraries, applies schema var remapping
- LSP: Same as CLI (libraries are typically not edited interactively)

**Fingerprinting**: Based on a hash of the serialized library data, or a version/timestamp embedded in the `.raylib` file.

##### SchemaVarAllocator

```rust
#[input]
struct SchemaVarAllocator(Arc<Mutex<TyVarAllocator>>);
```

A global allocator for schema type variables. Used by `mapped_def_types` to ensure that user-written type variables (`'a`, `'b`) are mapped to globally unique schema variables across the entire compilation.

**Set by**:
- CLI: Creates a fresh allocator at the start of each build
- LSP: Maintains one allocator across the session; allocator state is reset on full reanalysis

**Fingerprinting**: Not fingerprinted in the traditional sense. The allocator is stateful (monotonically increasing counter), but this doesn't affect correctness:
- `mapped_def_types` results are cached and reused when the definition hasn't changed
- When a definition changes, `mapped_def_types` recomputes and gets *new* schema var IDs
- Downstream queries (`typecheck_group`) see different IDs but produce equivalent results
- The schema var IDs are internal to typechecking; they never appear in user-facing output (reverse map converts back to user names like `'a`)

**Overflow**: The allocator uses a `u64` counter. Overflow is not a practical concern—even at 1M allocations/second, exhaustion would take ~580,000 years.

**Note**: The allocator is thread-safe (`Arc<Mutex<...>>`) to allow concurrent query execution in the future, but current implementation is single-threaded.

#### II. Queries

Queries are computed values derived from inputs or other queries. Each query is a pure function: given the same inputs, it produces the same output. The query system memoizes results and tracks dependencies to enable incremental recomputation.

##### Parsing (File-keyed)

- `parse(FileId)` → `ParseResult`

  **Dependencies**: `FileSource(FileId)` (input)

  **Semantics**:
  - Produces a syntactically valid AST even when errors are present (error recovery)
  - Assigns DefIds to top-level definitions as they are encountered
  - Assigns NodeIds to all AST nodes, scoped to their owning definition
  - Collects definition metadata and span mappings during the parse walk
  - Parse errors are collected but do not block downstream queries

  **Error handling**: Errors are returned in `ParseResult.errors`. The AST is still usable - missing or malformed nodes are represented with error placeholders, allowing partial analysis.

  **Invalidation**: Re-executes when `FileSource(FileId)` changes.

  **Definitions**:
  ```rust
  struct ParseResult {
      /// The parsed AST with DefIds and NodeIds assigned.
      pub ast: ast::File,

      /// All definitions in this file (flat list including impl members).
      pub defs: Vec<DefHeader>,

      /// Source mapping for all nodes (spans, doc comments, decorators, etc.).
      /// Reuses the existing SourceMap from ray-core/src/sourcemap.
      pub source_map: SourceMap,

      /// Parse errors encountered.
      pub errors: Vec<RayError>,
  }

  impl ParseResult {
      /// Returns all NodeIds belonging to a definition's body.
      /// Used by def_deps to iterate only over nodes within a specific definition,
      /// avoiding full-file traversal.
      fn nodes_in_def(&self, def_id: DefId) -> impl Iterator<Item = NodeId>;

      /// Returns the DefHeader for a definition.
      fn def_header(&self, def_id: DefId) -> &DefHeader;

      /// Returns the span for a node.
      fn span_of(&self, node_id: NodeId) -> Span;
  }

  struct DefHeader {
      pub def_id: DefId,
      pub name: String,
      pub kind: DefKind,
      pub span: Span,
      pub name_span: Span,  // Span of just the name (for rename)
      pub parent: Option<DefId>,  // For methods: the impl/trait DefId
  }

  enum DefKind {
      FileMain,   // Top-level execution context (local_index: 0)
      Function { signature: SignatureStatus },
      Constant { annotated: bool },  // annotated: true if type is explicit
      Method,     // Always has explicit signature (from trait or explicit)
      Struct,
      Trait,
      Impl,
      TypeAlias,
  }

  enum SignatureStatus {
      FullyAnnotated,  // All parameter and return types explicit
      ReturnElided,    // Parameters annotated, return type inferred from => body
      Unannotated,     // Missing parameter or return type annotations
  }
  ```

  **Annotated vs unannotated**: A function is "annotated" if its `SignatureStatus` is `FullyAnnotated` or `ReturnElided`. Both have enough information for callers to use without inference coupling. `Unannotated` functions require callers to be in the same SCC. See "The Binding Graph" section for details.

  **Name resolution invariant**: Cross-module references to `Unannotated` functions are errors. Name resolution checks `SignatureStatus` when resolving cross-module function references and produces `Resolution::Error` for unannotated functions. `DefKind::FileMain` is never exported or referenced by name - it exists only as the typing context for top-level statements. All other `DefKind` variants are unconditionally referenceable across modules.

- `file_ast(FileId)` → `FileAst`

  **Dependencies**: `parse(FileId)`, `name_resolutions(FileId)`, `struct_def(DefTarget)` for each struct referenced in curly expressions

  **Semantics**: Produces the transformed AST for a file. This is the primary AST representation used by most downstream queries. The raw `parse` result is an intermediate representation; `file_ast` applies syntactic and structural transformations that prepare the AST for typechecking.

  **Transformations performed**:

  1. **Compound assignment desugaring**: `x += 1` becomes `x = x + 1`. The `AssignOp` node is replaced with an `Assign` node whose RHS is a `BinOp` expression.

  2. **Function literal to closure**: Anonymous `fn` expressions (`Expr::Func`) are converted to `Expr::Closure`. This normalizes the representation for typechecking.

  3. **Curly shorthand expansion**: `Point { x }` becomes `Point { x: x }`. `CurlyElement::Name(n)` is converted to `CurlyElement::Labeled(n, Expr::Name(n))`.

  4. **Curly field ordering**: `Point { y: 1, x: 2 }` is reordered to match the struct definition's field order (e.g., `Point { x: 2, y: 1 }` if the struct defines `x` before `y`). This requires resolving `Point` via `name_resolutions` to find its `DefTarget`, then querying `struct_def(DefTarget)` to get the field order.

  **Error handling**: Transformation errors (e.g., unknown struct in curly expression) are collected in `FileAst.errors`. The transformation continues with partial results where possible.

  **Invalidation**: Re-executes when any dependency changes. Changes to struct definitions can invalidate `file_ast` for files that use those structs in curly expressions.

  **Definitions**:
  ```rust
  struct FileAst {
      /// The transformed AST.
      pub ast: ast::File,

      /// Source mapping (inherited from ParseResult, updated for synthetic nodes).
      pub source_map: SourceMap,

      /// Transformation errors.
      pub errors: Vec<RayError>,
  }
  ```

  **Usage**: Most queries that need the AST should depend on `file_ast`, not `parse`. Exceptions:
  - `file_imports(FileId)` - extracts imports from raw parse (no transformation needed)
  - `file_exports(FileId)` - extracts exports from raw parse (no transformation needed)
  - `name_resolutions(FileId)` - resolves names in raw parse (circular dependency otherwise)

- `file_imports(FileId)` → `Vec<ImportPath>`

  **Dependencies**: `parse(FileId)`

  **Semantics**: Extracts import statements from the AST. Returns raw import paths as written in source (not yet resolved to `ModulePath`s). Used by `resolved_imports` to perform module resolution.

  **Error handling**: Malformed import syntax is captured in parse errors; such imports are omitted from the result.

  **Invalidation**: Re-executes when `parse(FileId)` changes.

- `file_exports(FileId)` → `Vec<(String, DefId)>`

  **Dependencies**: `parse(FileId)`

  **Semantics**: Returns (name, DefId) pairs for all public definitions in the file. Used by `module_def_index` to build the module's namespace. Methods are not included (see "Method visibility").

  **Invalidation**: Re-executes when `parse(FileId)` changes.

##### Module Structure (from WorkspaceSnapshot)

These are direct lookups into the `WorkspaceSnapshot`, not computed queries:

- `files_in_module(ModulePath)` → `Vec<FileId>` - files belonging to a module
- `module_for_file(FileId)` → `ModulePath` - module containing a file
- `library_for_module(ModulePath)` → `Option<FilePath>` - precompiled library path

##### Name Resolution (File-keyed)

- `resolved_imports(FileId)` → `HashMap<String, Result<ModulePath, ImportError>>`

  **Dependencies**: `file_imports(FileId)`, `WorkspaceSnapshot`

  **Semantics**: Resolves each import statement to its target module. The key is the import alias (or module name if no alias), the value is the resolved `ModulePath` or an error.

  **Error handling**: Unresolvable imports produce `Err(ImportError)` in the result. Diagnostics are generated from these errors. Successfully resolved imports remain usable.

  **Definitions**:
  ```rust
  enum ImportError {
      UnknownModule(String),
      Ambiguous(Vec<ModulePath>),
  }
  ```
- `name_resolutions(FileId)` → `HashMap<NodeId, Resolution>`

  **Dependencies**: `parse(FileId)`, `resolved_imports(FileId)`, `module_def_index(ModulePath)` for the file's module and each imported module

  **Semantics**: Walks the indexed AST and resolves every name reference to a `Resolution`. This includes:
  - Top-level definitions (workspace or library) → `Resolution::Def(DefTarget)`
  - Local bindings (parameters, let-bindings, etc.) → `Resolution::Local(LocalBindingId)`
  - Unresolved or invalid → `Resolution::Error`

  The result is a **side table** mapping NodeIds to resolutions. The AST itself is never mutated; resolution is a separate data structure layered on top.

  **Error handling**: Unresolved names produce `Resolution::Error`. Cross-module references to unannotated functions also produce `Resolution::Error` with a diagnostic explaining the annotation requirement. This restriction is both intentional (encouraging explicit interfaces at module boundaries) and practical (avoiding cross-module inference cascades that would defeat incrementality)

  **Definitions**:
  ```rust
  /// What a name reference resolves to.
  enum Resolution {
      /// A top-level definition (function, struct, trait, etc.) - either workspace or library
      Def(DefTarget),
      /// A local binding (parameter, let-binding, etc.)
      Local(LocalBindingId),
      /// Unresolved (name error)
      Error,
  }

  /// Reference to a definition, either in the current workspace or external library.
  enum DefTarget {
      /// Definition in current workspace
      Workspace(DefId),
      /// Definition from external library
      External(ItemPath),
  }
  ```

  **Unified definition access**: Both workspace and library definitions are accessed through the same queries using `DefTarget`. For example, `def_scheme(DefTarget)` returns the type scheme regardless of whether the definition is in the workspace or a library. This unifies the lookup pattern - queries handle the `DefTarget` dispatch internally.

  This approach means:
  - Parsed AST is immutable and cacheable
  - Name resolution can be recomputed independently when imports change
  - LSP "what does this refer to" is a direct lookup in the side table

- `def_for_path(ItemPath)` → `Option<DefTarget>`

  **Dependencies**:
  - For workspace paths: `module_def_index(item_path.module)`, `parse(parent_def.file)` for method lookup
  - For library paths: `library_data(item_path.module)`

  **Semantics**: Looks up a definition by fully-qualified path. Returns `DefTarget::Workspace(DefId)` for workspace definitions or `DefTarget::External(ItemPath)` for library definitions. Used for:
  - Qualified references like `core::int::add`
  - Method lookup like `List::push`

  Performs syntactic canonicalization: strips type arguments (`List[int]::push` → `List::push`), normalizes path syntax.

  **Error handling**: Returns `None` if the path doesn't exist. Does not report diagnostics - callers decide how to handle missing definitions.

- `module_def_index(ModulePath)` → `HashMap<String, Result<DefId, NameCollision>>`

  **Dependencies**: `file_exports(FileId)` for each file in the module

  **Semantics**: Aggregates exports from all files in a module into a single namespace. Each name maps to either a unique DefId or a collision error.

  Method DefIds (both impl methods and trait methods) are **not** included. Methods are reachable only through:
  - Qualified paths: `Type::method` via `def_for_path(ItemPath)`
  - Call resolution: `x.method()` via `call_resolution(NodeId)` (type-directed)

  This reflects that methods are not "top-level names" in the module namespace - they're accessed through their parent type or trait.

  **Error handling**: If multiple definitions in a module export the same name (e.g., two files both define `fn helper()`), the entry for that name contains `Err(NameCollision)` rather than a DefId. This allows:
  - Other names in the module to resolve normally (graceful degradation)
  - Clear diagnostics showing which definitions collided and where
  - Deterministic behavior - the query result fully represents the ambiguity

  References to colliding names resolve to `Resolution::Error`, and a diagnostic is emitted listing the conflicting definitions.

  **Definitions**:
  ```rust
  struct NameCollision {
      pub name: String,
      pub definitions: Vec<DefId>,
  }
  ```

##### Type Definitions (DefTarget-keyed)

These queries take `DefTarget` to handle both workspace and library definitions uniformly.

- `struct_def(DefTarget)` → `StructDef`
- `trait_def(DefTarget)` → `TraitDef`
- `impl_def(DefTarget)` → `ImplDef`
- `type_alias(DefTarget)` → `TypeAliasDef`

  **Dependencies**:
  - For `DefTarget::Workspace(def_id)`: `parse(def_id.file)`, `name_resolutions(def_id.file)`
  - For `DefTarget::External(item_path)`: `library_data(item_path.module)`

  **Semantics**: Returns definition details for the given target. For workspace definitions, extracts from the indexed AST. For library definitions, looks up in `LibraryData`.

  **Error handling**: The target must correspond to the expected kind (e.g., `struct_def` requires a struct).

  **Definitions**:
  ```rust
  struct StructDef {
      pub target: DefTarget,
      pub name: String,
      pub type_params: Vec<TypeParam>,
      pub fields: Vec<FieldDef>,
  }

  struct FieldDef {
      pub name: String,
      pub ty: Ty,
  }

  struct TraitDef {
      pub target: DefTarget,
      pub name: String,
      pub type_params: Vec<TypeParam>,
      pub super_traits: Vec<DefTarget>,
      pub methods: Vec<DefTarget>,
  }

  struct ImplDef {
      pub target: DefTarget,
      pub type_params: Vec<TypeParam>,
      pub implementing_type: Ty,
      pub trait_ref: Option<DefTarget>,
      pub methods: Vec<DefTarget>,
  }

  struct TypeAliasDef {
      pub target: DefTarget,
      pub name: String,
      pub type_params: Vec<TypeParam>,
      pub aliased_type: Ty,
  }
  ```

- `impls_in_module(ModulePath)` → `Vec<DefId>`

  **Dependencies**: `parse(FileId)` for all files in `files_in_module(ModulePath)`

  **Semantics**: Collects all `DefKind::Impl` DefIds from all files in the module.

  **Invalidation**: Any file change in the module invalidates this query. This is a known invalidation hotspot - changing any file causes re-enumeration of all impls in the module.

  **Error handling**: Returns empty vec if module has no impl blocks.

- `traits_in_module(ModulePath)` → `Vec<DefId>`

  **Dependencies**: `parse(FileId)` for all files in `files_in_module(ModulePath)`

  **Semantics**: Collects all `DefKind::Trait` DefIds from all files in the module.

  **Invalidation**: Same as `impls_in_module` - any file change invalidates.

  **Error handling**: Returns empty vec if module has no traits.

- `impls_for_type(DefTarget)` → `ImplsForType`

  **Dependencies**:
  - For workspace types: `impls_in_module(ModulePath)` for each module, `impl_def(DefTarget)` for each impl
  - For library types: `library_data(ModulePath)` for each loaded library

  **Semantics**: Returns all impl blocks where `implementing_type` matches the given type, separated into inherent impls and trait impls. Searches both workspace and all loaded libraries.

  **Error handling**: Returns empty vecs if no impls exist.

  **Definitions**:
  ```rust
  struct ImplsForType {
      pub inherent: Vec<DefTarget>,     // impl Foo { ... }
      pub trait_impls: Vec<DefTarget>,  // impl Trait for Foo { ... }
  }
  ```

- `impls_for_trait(DefTarget)` → `Vec<DefTarget>`

  **Dependencies**:
  - For workspace traits: `impls_in_module(ModulePath)` for each module, `impl_def(DefTarget)` for each impl
  - For library traits: `library_data(ModulePath)` for each loaded library

  **Semantics**: Returns all impl blocks where `trait_ref` matches the given trait. Searches both workspace and all loaded libraries.

  **Error handling**: Returns empty vec if no impls exist for the trait.

##### Binding Analysis

- `def_deps(DefId)` → `Vec<DefId>`

  **Dependencies**: `parse(def_id.file)`, `name_resolutions(def_id.file)`

  **Semantics**: Returns all same-module DefIds that this definition syntactically references. Uses `parse(file).nodes_in_def(def_id)` to iterate only over nodes within this definition's body, then looks up each node in `name_resolutions` to find references.

  **Note**: This query is workspace-only. Library definitions are already typechecked and don't participate in binding analysis.

  **Error handling**: References to `Resolution::Error` or `Resolution::Local` are skipped. References to `DefTarget::External` are skipped (library calls don't create binding edges). Only `DefTarget::Workspace` creates edges, and only for DefIds in the same module.

- `binding_graph(ModulePath)` → `BindingGraph`

  **Dependencies**: `def_deps(DefId)` for all DefIds in the module, `parse` for all files in the module

  **Semantics**: Builds the binding graph for SCC computation by aggregating dependencies from all files in the module.

  **Construction**:
  1. Collect all DefIds from all files in the module via `parse(FileId)` for each file in `files_in_module(ModulePath)`
  2. For each DefId, query `def_deps(DefId)` to get its raw dependencies
  3. Filter edges to **inference edges only**

  **Edge filtering**: An edge A → B from `def_deps` is included in the binding graph only if B is unannotated - i.e., B is `DefKind::Function { signature: Unannotated }`, `DefKind::Constant { annotated: false }`, or `DefKind::FileMain`. References to annotated functions, annotated constants, structs, traits, etc. are excluded.

  Note: `def_deps(DefId)` returns all syntactic references. The inference-edge filtering happens in `binding_graph`, not in `def_deps`. This keeps `def_deps` useful for other purposes (e.g., "find references" needs all edges, not just inference edges).

  **Nodes**: All definitions in the module are nodes, regardless of whether they have outgoing edges. Annotated definitions that only reference other annotated definitions have no outgoing edges and become singleton SCCs.

  **Cross-file groups**: Since the graph aggregates from all files in the module, an SCC may contain DefIds from different files. For example, if `file_a.ray` defines unannotated `fn foo()` that calls unannotated `fn bar()` in `file_b.ray`, and `bar` calls `foo`, they form a single binding group spanning both files.

  **Error handling**: If a file has parse errors, its DefIds are still included (from the recovered AST). Definitions with incomplete information due to parse errors still participate in the binding graph - they may have fewer edges than they would otherwise, but they're not excluded.

- `binding_groups(ModulePath)` → `Vec<BindingGroupId>`

  **Dependencies**: `binding_graph(ModulePath)`

  **Semantics**: Computes strongly connected components of the binding graph using Tarjan's algorithm. Returns group IDs in topological order (dependencies before dependents). Every definition in the module appears in exactly one group.

  **Error handling**: N/A - pure graph computation.

- `binding_group_members(BindingGroupId)` → `Vec<DefId>`

  **Dependencies**: `binding_groups(ModulePath)` (the group ID contains the module)

  **Semantics**: Returns the DefIds belonging to the specified binding group. For singleton groups (annotated definitions with no unannotated dependencies), returns a single DefId.

  **Error handling**: N/A - direct lookup.

- `binding_group_for_def(DefId)` → `BindingGroupId`

  **Dependencies**: `binding_groups(module_for_file(def_id.file))`

  **Semantics**: Returns the binding group containing a given definition. This is the inverse of `binding_group_members`. Computed by building a reverse index from `binding_groups` + `binding_group_members`.

  **Error handling**: Panics if the DefId is not found in any group (internal error - every definition should be in exactly one group).

##### Closure Analysis

- `closure_info(NodeId)` → `Option<ClosureInfo>`

  **Dependencies**: `parse(node_id.owner.file)`, `name_resolutions(node_id.owner.file)`

  **Semantics**: For a closure expression NodeId, returns capture analysis. Returns `None` if the NodeId is not a closure.

  **Error handling**: N/A - pure analysis.

  **Definitions**:
  ```rust
  struct ClosureInfo {
      pub parent: DefId,
      pub captures: Vec<LocalBindingId>,
  }
  ```

##### Typechecking

- `mapped_def_types(DefId)` → `MappedDefTypes`

  **Dependencies**: `file_ast(def_id.file)`, global `SchemaVarAllocator` input

  **Semantics**: Maps user-written type variables (e.g., `'a`, `'b`) in a definition's annotations to globally unique schema variables. This ensures that `'a` in one definition doesn't collide with `'a` in another definition during typechecking.

  Type variables are definition-scoped: `'a` in `fn foo<'a>` is distinct from `'a` in `fn bar<'a>`. The global `SchemaVarAllocator` ensures uniqueness across the entire compilation.

  The query produces both forward and reverse mappings:
  - Forward (`var_map`): Used during typechecking to substitute user vars with schema vars
  - Reverse (`reverse_map`): Used during error reporting and pretty-printing to display user-friendly names

  **Error handling**: N/A - pure transformation. Invalid type variable references are caught during name resolution.

  **Definitions**:
  ```rust
  struct MappedDefTypes {
      /// Forward: user type var -> schema var
      pub var_map: HashMap<TyVar, TyVar>,
      /// Reverse: schema var -> user type var (for pretty printing)
      pub reverse_map: HashMap<TyVar, TyVar>,
      /// Mapped types by NodeId (type annotations in the definition)
      pub types: HashMap<NodeId, Ty>,
      /// Mapped signature scheme (if the definition is annotated)
      pub signature: Option<TyScheme>,
  }
  ```

- `typecheck_group(BindingGroupId)` → `TypecheckResult`

  **Dependencies**: `binding_group_members(BindingGroupId)`, `file_ast` for each member's file, `name_resolutions` for each member's file, `mapped_def_types(DefId)` for each member, `closure_info` for closures in the group, `def_scheme(DefTarget)` for dependencies outside the group

  **Semantics**: Typechecks all definitions in the binding group together. For unannotated definitions, infers type schemes. For annotated definitions, checks the body against the declared scheme. Produces type assignments for all NodeIds in the group's definitions.

  **Error handling**: Returns diagnostics for type errors (mismatches, unresolved constraints, etc.). Type errors don't prevent the query from completing - it returns best-effort types for error recovery.

  **Definitions**:
  ```rust
  struct TypecheckResult {
      pub schemes: HashMap<DefId, TyScheme>,
      pub node_types: HashMap<NodeId, Ty>,
      pub errors: Vec<RayError>,
  }
  ```

- `def_scheme(DefTarget)` → `TyScheme`

  **Dependencies**:
  - For `DefTarget::Workspace(def_id)`: `binding_group_for_def(def_id)`, `typecheck_group(BindingGroupId)` for the resulting group
  - For `DefTarget::External(item_path)`: `library_data(item_path.module)`

  **Semantics**: Returns the type scheme for a definition. For workspace definitions, this is either the declared scheme (annotated) or inferred scheme (unannotated). For library definitions, returns the precomputed scheme from `LibraryData`.

  **Error handling**: Returns an error type if the definition failed to typecheck. Library definitions never fail (they were successfully compiled).

- `ty_of(NodeId)` → `Ty`

  **Dependencies**: `binding_group_for_def(node_id.owner)`, `typecheck_group(BindingGroupId)` for the resulting group

  **Semantics**: Returns the monomorphic type for an expression node. All expression nodes have a type after typechecking completes.

  **Error handling**: Returns an error type if typechecking failed for the containing definition.

##### Call Resolution

- `call_resolution(NodeId)` → `Option<CallResolution>`

  **Dependencies**: `binding_group_for_def(node_id.owner)`, `typecheck_group(BindingGroupId)` for the resulting group

  **Semantics**: For a call expression NodeId, returns resolution information if the call required method/trait resolution. This includes method calls (`x.method()`), operator calls (`a + b`), and index expressions (`a[i]`).

  Returns `None` for direct function calls that don't go through method resolution.

  **Error handling**: Unresolvable method calls produce type errors during typechecking; this query only stores successful resolutions.

  **Definitions**:
  ```rust
  struct CallResolution {
      pub target: DefTarget,
      pub poly_callee_ty: TyScheme,
      pub callee_ty: TyScheme,
      pub subst: Subst,
  }
  ```

  Note: `DefTarget` is defined in the Name Resolution section above.

##### Source Mapping & Spans

- `span_of(NodeId)` → `Span`

  **Dependencies**: `parse(node_id.owner.file)`

  **Semantics**: Returns the source span for any AST node. The span includes start/end line and column.

  **Error handling**: Panics if the NodeId doesn't exist (internal error).

- `file_of(NodeId)` → `FileId`

  **Semantics**: Extracts the FileId from a NodeId. This is a pure computation on the NodeId structure, not a query.

- `find_at_position(FileId, line, col)` → `Option<NodeId>`

  **Dependencies**: `parse(FileId)`

  **Semantics**: Finds the most specific (smallest span) NodeId containing the given position. Used by LSP for hover, go-to-definition, etc.

  **Error handling**: Returns `None` if no node contains the position.

- `decorators(DefId)` → `Vec<Decorator>`

  **Dependencies**: `parse(def_id.file)`

  **Semantics**: Returns decorators attached to a definition (e.g., `@intrinsic`, `@inline`).

  **Error handling**: Returns empty vec if no decorators.

- `has_decorator(DefId, name)` → `bool`

  **Dependencies**: `decorators(DefId)`

  **Semantics**: Convenience query that checks if a definition has a specific decorator.

- `doc_comment(DefId)` → `Option<String>`

  **Dependencies**: `parse(def_id.file)`

  **Semantics**: Returns the doc comment attached to a definition, if any.

  **Error handling**: Returns `None` if no doc comment.

##### Symbol Resolution (for LSP)

- `symbol_targets(NodeId)` → `Vec<SymbolTarget>`

  **Dependencies**: `name_resolutions(node_id.owner.file)`, `call_resolution(NodeId)`, `parse(target_def.file)` for each resolved target DefId

  **Semantics**: For a NodeId (typically a name reference), returns go-to-definition targets. Multiple targets occur when both trait definition and impl are relevant (e.g., clicking on a method call might show both the trait method signature and the impl).

  **Error handling**: Returns empty vec if the NodeId has no resolvable targets.

  **Definitions**:
  ```rust
  struct SymbolTarget {
      pub path: ItemPath,
      pub location: SourceLocation,  // Handles both workspace and library targets
      pub role: SymbolRole,
  }

  enum SymbolRole {
      Definition,
      Reference,
  }
  ```

  Note: `SourceLocation` is defined in `DefinitionRecord` and handles both workspace (`FileId + Span`) and library (`FilePath + Span`) targets.

- `def_name(DefTarget)` → `String`

  **Dependencies**: For `Workspace(DefId)`: `parse(def_id.file)`. For `External(ItemPath)`: `library_data`.

  **Semantics**: Convenience query returning the simple name of a definition (e.g., `push` for a method, `List` for a struct). Works for both workspace and library definitions.

- `def_path(DefTarget)` → `ItemPath`

  **Dependencies**: For `Workspace(DefId)`: `parse(def_id.file)`, `module_for_file(def_id.file)`. For `External(ItemPath)`: returns the path directly.

  **Semantics**: Convenience query constructing the fully-qualified path for a definition by combining the module path with the definition's name (and parent type/trait for methods).

- `definition_record(DefTarget)` → `DefinitionRecord`

  **Dependencies**: `def_path(DefTarget)`, `doc_comment` (workspace only), `parse` or `library_data` for span and kind

  **Semantics**: Convenience aggregation of definition metadata for hover info. Combines path, location, documentation, and kind into a single record. For library definitions, uses metadata from `LibraryData.definitions`.

  **Definitions**:
  ```rust
  struct DefinitionRecord {
      pub path: ItemPath,
      pub source_location: Option<SourceLocation>,  // Location for go-to-definition
      pub doc: Option<String>,
      pub kind: DefKind,
  }

  enum SourceLocation {
      /// Workspace definition with known FileId
      Workspace { file: FileId, span: Span },
      /// Library definition with original source path (for source navigation)
      Library { filepath: FilePath, span: Span },
  }
  ```

  For library definitions, `source_location` contains the original source path from when the library was compiled. This enables go-to-definition to library sources when available. Libraries serialize the `FilePath` and `Span` in `LibraryData.definitions`.

##### IDE Features (for LSP)

- `semantic_tokens(FileId)` → `SemanticTokens`

  **Dependencies**: `parse(FileId)`, `name_resolutions(FileId)`, optionally `ty_of(NodeId)` for type-aware coloring

  **Semantics**: Produces a list of semantic tokens for syntax highlighting. Each token has a span, token type (e.g., function, variable, type, keyword), and optional modifiers (e.g., definition, mutable). Used by LSP `textDocument/semanticTokens/full`.

  **Error handling**: Returns tokens for successfully parsed portions of the file. Parse errors don't prevent token generation for valid AST nodes.

  **Definitions**:
  ```rust
  struct SemanticTokens {
      pub data: Vec<SemanticToken>,
  }

  struct SemanticToken {
      pub delta_line: u32,
      pub delta_start: u32,
      pub length: u32,
      pub token_type: SemanticTokenType,
      pub modifiers: SemanticTokenModifiers,
  }

  enum SemanticTokenType {
      Function,
      Variable,
      Parameter,
      Type,
      Struct,
      Trait,
      Property,  // field access
      Method,
      Keyword,
      String,
      Number,
      Comment,
  }
  ```

- `scope_at(FileId, Position)` → `Vec<(String, ScopeEntry)>`

  **Dependencies**: `parse(FileId)`, `name_resolutions(FileId)`, `resolved_imports(FileId)`, `module_def_index(ModulePath)` for the file's module

  **Semantics**: Returns all names in scope at a given position in the file. This includes:
  - Local bindings (parameters, let-bindings) visible at the position
  - Top-level definitions from the current file
  - Imports (module aliases and imported names)
  - Definitions from sibling files in the same module

  The result is used by completion to populate scope-based suggestions.

  **Error handling**: Returns partial results when some names couldn't be resolved (e.g., due to parse errors in imported modules).

  **Definitions**:
  ```rust
  enum ScopeEntry {
      Local(LocalBindingId),
      Def(DefTarget),
      Module(ModulePath),
  }
  ```

- `expected_type_at(FileId, Position)` → `Option<Ty>`

  **Dependencies**: `parse(FileId)`, `ty_of(NodeId)` for surrounding context, `def_scheme(DefTarget)` for function parameter types

  **Semantics**: Infers the expected type at a position based on surrounding context. Returns `Some(ty)` when the position is:
  - A function argument position → parameter type from callee's scheme
  - Right-hand side of an assignment → type of left-hand side
  - Return expression → declared return type of enclosing function
  - Element in a list literal → element type if list type is known

  Returns `None` when no type expectation can be inferred.

  **Error handling**: Returns `None` if the surrounding context has type errors.

- `completion_context(FileId, Position)` → `Option<CompletionContext>`

  **Dependencies**: `parse(FileId)`, `scope_at(FileId, Position)`, `expected_type_at(FileId, Position)`, `ty_of(NodeId)` for receiver type

  **Semantics**: Analyzes the cursor position to determine what kind of completion is appropriate. The result includes:
  - The completion kind (member access, scope, module member, type member)
  - Current scope (for scope-based completion)
  - Receiver type (for member access after `.`)
  - Expected type (for ranking results by compatibility)

  **Error handling**: Returns `None` if the position doesn't support completion (e.g., inside a string literal or comment).

  **Definitions**:
  ```rust
  struct CompletionContext {
      pub kind: CompletionKind,
      pub scope: Vec<(String, ScopeEntry)>,
      pub receiver_type: Option<Ty>,
      pub expected_type: Option<Ty>,
  }

  enum CompletionKind {
      /// After `.` - complete methods/fields on receiver
      Member,
      /// Bare identifier - complete from scope
      Scope,
      /// After `module::` - complete module exports
      ModuleMember(ModulePath),
      /// After `Type::` - complete associated items
      TypeMember(DefTarget),
  }
  ```

- `methods_for_type(Ty)` → `Vec<(String, DefTarget)>`

  **Dependencies**: `impls_for_type(DefTarget)` for the type, `impl_def(DefTarget)` for each impl, `trait_def(DefTarget)` for trait method signatures

  **Semantics**: Returns all methods available on a type, including:
  - Inherent methods (from `impl Type { ... }` blocks)
  - Trait methods (from `impl Trait for Type { ... }` blocks)

  Methods are returned as (name, DefTarget) pairs. For trait methods, the DefTarget points to the impl method (not the trait signature). Methods from library types return `DefTarget::External`.

  **Error handling**: Returns empty vec if the type has no methods or if the type is `Ty::Error`.

- `associated_items(DefTarget)` → `Vec<(String, DefTarget)>`

  **Dependencies**: For workspace types: `parse(def_id.file)`, `impls_for_type(DefTarget)`. For library types: `library_data(module)`.

  **Semantics**: Returns associated items accessible via `Type::` syntax:
  - Static methods (methods with no `self` parameter)
  - Associated constants
  - Constructors (by convention, methods named `new` or similar)

  This differs from `methods_for_type` which returns instance methods accessible via `.` syntax.

  **Error handling**: Returns empty vec if the target is not a type definition.

##### Operators

Operators in Ray are methods with symbolic names (e.g., `+`, `-`, `*`). A trait defines an operator by declaring a method with that symbol as its name. For example, a trait with `fn +(self, other: Self) -> Self` defines the `+` operator.

- `operator_index()` → `HashMap<String, OperatorEntry>`

  **Dependencies**: `traits_in_module(ModulePath)` for each module in workspace, `trait_def(DefTarget)` for each trait, `library_data(ModulePath)` for each loaded library

  **Semantics**: Scans all traits in the workspace AND loaded libraries for methods with symbolic (non-alphanumeric) names. Builds a map from operator symbol to the trait and method that define it. Most operators (like `+`, `-`, `*`) are defined in the core library.

  **Invalidation**: Any file change that affects `traits_in_module` invalidates this index. Library operators are stable (libraries don't change during a session).

  **Error handling**: If multiple traits define the same operator symbol, this is an error (ambiguous operator). The index stores the first definition and records the conflict.

  **Definitions**:
  ```rust
  struct OperatorEntry {
      pub trait_def: DefTarget,
      pub method_def: DefTarget,
      pub arity: OperatorArity,
  }

  enum OperatorArity {
      Prefix,  // unary: -x, !x
      Infix,   // binary: a + b, a * b
  }
  ```

- `lookup_infix_op(symbol: &str)` → `Option<OperatorEntry>`

  **Dependencies**: `operator_index()`

  **Semantics**: Looks up a binary operator symbol in the operator index. Returns the trait and method that define it.

  **Error handling**: Returns `None` if the operator symbol is not defined by any trait.

- `lookup_prefix_op(symbol: &str)` → `Option<OperatorEntry>`

  **Dependencies**: `operator_index()`

  **Semantics**: Looks up a unary operator symbol in the operator index. Returns the trait and method that define it.

  **Error handling**: Returns `None` if the operator symbol is not defined by any trait.

##### Builtins

Builtins are well-known types that the compiler needs to reference for language features. They are resolved through normal name resolution, not special-cased.

- `builtin_ty(name: &str)` → `Option<DefTarget>`

  **Dependencies**: `def_for_path(ItemPath)` for the builtin's expected path

  **Semantics**: Looks up well-known types by name. Returns `DefTarget` since builtins are typically from the core library (`DefTarget::External`). The lookup uses a fixed mapping from builtin name to expected module path:
  - `"string"` → `def_for_path("core::string::string")`
  - `"Index"` → `def_for_path("core::ops::Index")`
  - `"Iterator"` → `def_for_path("core::iter::Iterator")`
  - etc.

  If the expected path doesn't exist (e.g., in a no-core build), returns `None`. User code can define these types if needed.

  **Error handling**: Returns `None` if the builtin type is not found at the expected path.

### D. Error/Diagnostics Handling

The query system handles errors through a **stored-not-propagated** model. Errors are recorded where they are discovered, not passed through the call chain. This avoids the problem of multiple callers all trying to propagate the same error.

#### Principles

1. **Errors live in query results**: Queries that can produce errors include an `errors: Vec<RayError>` field (or similar) in their result type. The error is stored once, at the point of discovery.

2. **Callers don't propagate errors**: When a query depends on another query that produced errors, the caller does not copy or re-report those errors. The original query already recorded them.

3. **Callers react with sentinel values**: When errors occur, callers continue with degraded values:
   - Name resolution returns `Resolution::Error` for unresolvable names
   - Type inference uses `Ty::Error` as a "poison" type that unifies with anything
   - Scheme lookup returns `TyScheme::Error` for definitions that failed to typecheck

4. **Single aggregation point**: The `file_diagnostics(FileId)` query collects all errors affecting a file exactly once. CLI/LSP calls this explicitly to retrieve diagnostics for display.

#### Sentinel Values

Each pipeline stage has its own error sentinel:

| Stage | Sentinel | Meaning |
|-------|----------|---------|
| Name resolution | `Resolution::Error` | Name couldn't be resolved |
| Type inference | `Ty::Error` | Type couldn't be determined |
| Scheme lookup | `TyScheme::Error` | Definition failed to typecheck |

Sentinels are "sticky" - they propagate through computations without generating additional errors. For example, if `x` has type `Ty::Error`, then `x + 1` also has type `Ty::Error`, but no new error is reported (the original error was already recorded during name resolution or wherever `x` got its error type).

#### Error Types

Errors use the existing `RayError` type from `ray-core/src/errors`:

```rust
pub struct RayError {
    pub msg: String,
    pub src: Vec<Source>,       // Spans where error occurred
    pub kind: RayErrorKind,
    pub context: Option<String>,
}

pub enum RayErrorKind {
    Parse,
    UnexpectedToken,
    Name,       // Name resolution errors
    Import,     // Import resolution errors
    Compile,    // General compilation errors
    Link,
    Type,       // Type checking errors
    IO,
    Unknown,
}
```

Different queries produce errors with appropriate kinds:
- `parse` → `RayErrorKind::Parse`, `RayErrorKind::UnexpectedToken`
- `resolved_imports` → `RayErrorKind::Import`
- `name_resolutions` → `RayErrorKind::Name`
- `typecheck_group` → `RayErrorKind::Type`

#### Query Results with Errors

Queries that can fail include errors in their result. For example, `ParseResult` and `TypecheckResult` both include `errors: Vec<RayError>` (see `parse` and `typecheck_group` queries).

Some queries use `Result` for optional values with errors:

```rust
// resolved_imports returns per-import results
fn resolved_imports(FileId) -> HashMap<String, Result<ModulePath, ImportError>>;

// module_def_index returns per-name results
fn module_def_index(ModulePath) -> HashMap<String, Result<DefId, NameCollision>>;
```

These per-item results allow partial success - one failed import doesn't prevent other imports from resolving.

#### Diagnostic Aggregation

```rust
/// Collects all diagnostics for a file from all pipeline stages.
fn file_diagnostics(FileId) -> Vec<RayError>;
```

**Dependencies**: `parse(FileId)`, `resolved_imports(FileId)`, `name_resolutions(FileId)`, `binding_group_for_def(DefId)` for each DefId in the file, `typecheck_group(BindingGroupId)` for each resulting group

**Semantics**: Walks all queries that can produce errors for a file and collects their error lists. Each error appears exactly once - there's no deduplication because errors are never duplicated in the first place.

**Order**: Errors are returned in pipeline order (parse → imports → names → types), then by source location within each stage. This provides predictable output for testing and display.

**Usage**:
- CLI calls `file_diagnostics(file)` for each file after compilation completes
- LSP calls `file_diagnostics(file)` after each edit to update diagnostics

#### Error Recovery Strategy

The system prioritizes **continuing analysis** over **failing fast**:

1. **Parse errors**: The parser produces a partial AST with error nodes. Indexing proceeds, assigning DefIds even to malformed definitions.

2. **Import errors**: Unresolved imports produce `ImportError` but don't block name resolution for other imports.

3. **Name errors**: Unresolved names become `Resolution::Error`. Typechecking proceeds using `Ty::Error` for the unresolved reference.

4. **Type errors**: Type mismatches and unresolved constraints are recorded. The definition gets `TyScheme::Error` and dependents use `Ty::Error`.

This cascading-with-sentinels approach means:
- A single typo doesn't prevent the entire file from being analyzed
- LSP can provide hover/completion even in files with errors
- Errors are localized to affected definitions, not propagated globally

## 4. Integration

### A. CLI

The CLI integrates with the query system through two commands: `ray build` (compilation) and `ray analyze` (diagnostics only). Both use the same underlying query infrastructure.

#### I. Workspace Discovery

The CLI builds a `WorkspaceSnapshot` based on what's passed to it:

| Input | Behavior |
|-------|----------|
| Single file (`ray build foo.ray`) | Entry file is `foo.ray`. Determines if this is a single-file module or part of a directory module (by checking for sibling `.ray` files). If part of a directory module, discovers siblings. Resolves imports to find dependencies. |
| Directory (`ray build src/`) | Scans for `.ray` files in the directory tree. Entry is determined by convention (e.g., `main.ray` or single file). |
| Multiple files (`ray build a.ray b.ray`) | Each file is processed. Common module structure is inferred from paths. |
| No arguments (`ray build`) | Looks for `ray.toml` in current directory or ancestors. If found, uses its configuration. Otherwise, scans current directory. |

**Module discovery**: The existing `ModuleBuilder::resolve_module_path` logic walks upward from a file to find module boundaries. A directory is a module directory if it contains `.ray` files. Single-file modules are detected when the parent directory isn't a module directory.

**Library resolution**: Import paths are resolved against:
1. Sibling files in the same module
2. Subdirectories (submodules)
3. Search paths from environment or `ray.toml`
4. Precompiled `.raylib` files in library directories

#### II. Commands

**`ray analyze`**: Semantic analysis output (text or JSON).

```rust
fn analyze(options: AnalyzeOptions) -> AnalysisReport {
    let snapshot = build_snapshot(&options.input_path, search_paths);
    let db = Database::new(&snapshot);

    // Collect diagnostics from all files
    let mut diagnostics = Vec::new();
    for file_id in snapshot.all_files() {
        diagnostics.extend(file_diagnostics(&db, file_id));
    }

    // Collect symbols (functions, structs, traits, type aliases)
    let mut symbols = Vec::new();
    for file_id in snapshot.all_files() {
        let parsed = parse(&db, file_id);
        for header in &parsed.defs {
            let def_id = header.def_id;
            let target = DefTarget::Workspace(def_id);
            symbols.push(SymbolInfo {
                id: def_id,
                name: header.name.clone(),
                kind: header.kind,
                filepath: snapshot.file_path(file_id),
                span: header.span,
                ty: def_scheme(&db, target).to_string(),
                doc: doc_comment(&db, def_id),
            });
        }
    }

    // Collect types for all expressions
    let mut types = Vec::new();
    for file_id in snapshot.all_files() {
        let parsed = parse(&db, file_id);
        for header in &parsed.defs {
            for node_id in parsed.nodes_in_def(header.def_id) {
                let ty = ty_of(&db, node_id);
                if !ty.is_error() {
                    types.push(TypeInfo {
                        id: node_id,
                        filepath: snapshot.file_path(file_id),
                        span: parsed.span_of(node_id),
                        ty: ty.to_string(),
                    });
                }
            }
        }
    }

    // Collect definition links (usage -> definition)
    let mut definitions = Vec::new();
    for file_id in snapshot.all_files() {
        let parsed = parse(&db, file_id);
        let resolutions = name_resolutions(&db, file_id);
        for (node_id, resolution) in resolutions {
            definitions.push(DefinitionInfo {
                usage_id: node_id,
                usage_span: parsed.span_of(node_id),
                definition: resolution.to_def_id(),
            });
        }
    }

    AnalysisReport { diagnostics, symbols, types, definitions }
}
```

Output: `AnalysisReport` containing diagnostics, symbols, types, and definition links. Emitted as text or JSON depending on `--format`.

**`ray build`**: Compilation to `.raylib` or executable.

```rust
fn build(options: BuildOptions) -> Result<(), Vec<RayError>> {
    let snapshot = build_snapshot(&options.input_path, search_paths);
    let db = Database::new(&snapshot);

    // Check for errors
    let mut errors = Vec::new();
    for file_id in snapshot.all_files() {
        errors.extend(file_diagnostics(&db, file_id));
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    // Generate LIR (pulls parsed AST, type info, closure analysis from db)
    let lir = lir::generate(&db, &snapshot);

    if options.build_lib {
        // Library: serialize LIR + type schemes + source maps
        let lib = libgen::serialize(
            lir,
            &db,  // for schemes, source maps
            &snapshot,
        );
        fs::write(options.output_path, lib)?;
    } else {
        // Executable: monomorphize and codegen to LLVM
        lir.monomorphize();
        llvm::codegen(&lir, &db, options.target, options.output_path)?;
    }

    Ok(())
}
```

Output: `.raylib` file (library) or executable binary.

**Fresh database per build**: The CLI creates a new `Database` for each invocation. In-memory caching provides benefit within a single build (e.g., shared dependencies parsed once), but there's no persistence across builds without a workspace cache.

#### III. Cache

**Prerequisite**: Persistent caching is only enabled when a `ray.toml` file exists at the workspace root. Without explicit workspace configuration, the CLI operates without disk caching.

**Cache location**: `.ray/cache/` relative to `ray.toml`.

**Format**: Bincode serialization (same as `.raylib` files).

**Directory structure**:
```
.ray/
  cache/
    version                      # Cache format version (integer)
    parse/
      <path_hash>.bin            # ParseResult for a file
    name_resolutions/
      <path_hash>.bin            # Name resolution results for a file
    binding_graph/
      <module_hash>.bin          # Binding graph for a module
    typecheck_group/
      <group_key_hash>.bin       # Typecheck results for a binding group
    ...
```

File-keyed queries use a hash of the file's relative path (from workspace root). Module-keyed queries use a hash of the module path. This ensures cache filenames are stable across builds regardless of FileId assignment order.

**What's stored per cache entry**:

Each `.bin` file contains:
```rust
struct CacheEntry<K, V> {
    key: K,                           // Query key (e.g., file path, module path)
    value: V,                         // Serialized query result
    fingerprint: u128,                // Hash of the result value
    dependencies: Vec<Dependency>,    // What this result depends on
}

struct Dependency {
    query: QueryId,                   // Which query
    key_hash: u64,                    // Hash of the dependency's key
    fingerprint: u128,                // Fingerprint at computation time
}
```

**Validation (red-green algorithm)**:

On cache lookup for a query:
1. Find the cache file by hashing the query key
2. If no file exists → cache miss, compute fresh
3. If file exists, for each recorded dependency:
   - Recursively validate the dependency (may itself hit cache or recompute)
   - Compare the dependency's current fingerprint to the stored one
4. If all fingerprints match → **green**, return cached result
5. If any mismatch → **red**, recompute this query

**Early exit optimization**: If a query recomputes but produces the same fingerprint as before, downstream queries that depend on it remain valid. This prevents unnecessary cascading when changes don't affect outputs.

**Population**: Building automatically populates the cache. After computing a query result, it's written to disk with its fingerprint and dependency list.

**Version invalidation**: The `version` file contains a format version number. If the version doesn't match the compiler's expected version, the entire cache is discarded. This version must be incremented whenever:
- Cache entry format changes
- Query semantics change in ways that affect cached results
- Fingerprint computation changes

#### IV. Library Generation

When building a library (`ray build --lib`), the CLI collects data from query results to create a `.raylib` file. This is the inverse of loading a library - instead of reading `LibraryData` from disk, we serialize query results into the format.

**Data collection from queries**:

```rust
fn build_library_data(db: &Database, module_path: &ModulePath) -> LibraryData {
    let mut lib = LibraryData::default();

    // Collect all definitions from the module
    for file_id in files_in_module(db, module_path) {
        let parsed = parse(db, file_id);
        for def_header in &parsed.defs {
            let def_id = def_header.def_id;
            let target = DefTarget::Workspace(def_id);
            let item_path = def_path(db, def_id);

            // Type scheme (for all exported definitions)
            let scheme = def_scheme(db, target);
            lib.schemes.insert(item_path.clone(), scheme);

            // Definition-specific data
            match def_header.kind {
                DefKind::Struct { .. } => {
                    lib.structs.insert(item_path.clone(), struct_def(db, target));
                }
                DefKind::Trait { .. } => {
                    lib.traits.insert(item_path.clone(), trait_def(db, target));
                }
                DefKind::Impl { .. } => {
                    let impl_def = impl_def(db, target);
                    lib.impls.insert(item_path.clone(), impl_def.clone());

                    // Build impl indexes
                    let type_path = type_to_item_path(&impl_def.implementing_type);
                    lib.impls_by_type
                        .entry(type_path)
                        .or_default()
                        .push(item_path.clone());

                    if let Some(trait_ref) = &impl_def.trait_ref {
                        let trait_path = def_target_to_item_path(trait_ref);
                        lib.impls_by_trait
                            .entry(trait_path)
                            .or_default()
                            .push(item_path.clone());
                    }
                }
                _ => {}
            }

            // IDE metadata
            lib.definitions.insert(
                item_path,
                build_definition_record(db, def_id, def_header),
            );
        }
    }

    // Operator tables (extract operators defined by traits in this module)
    lib.operators = extract_module_operators(db, module_path);
    // Note: extract_module_operators scans traits_in_module(module_path),
    // not the global operator_index() which includes library operators

    // Source maps (for error messages)
    for file_id in files_in_module(db, module_path) {
        let parsed = parse(db, file_id);
        lib.source_map.extend(parsed.source_map);
    }

    // Module list
    lib.modules = vec![module_path.clone()];

    lib
}
```

**Serialization format**: The `LibraryData` structure is serialized using bincode, with a header containing:
- Format version (for compatibility checking on load)
- Max schema var ID used (for remapping on load)
- Module path

**LIR inclusion**: The `.raylib` file also includes LIR for linking. LIR generation is out of scope for this document, but the library file format includes a slot for it:

```rust
struct RayLibFile {
    pub header: LibraryHeader,
    pub data: LibraryData,
    pub lir: lir::Program,  // Generated by codegen, not frontend
}
```

### B. LSP

The LSP integrates with the query system to provide interactive features: diagnostics, hover, go-to-definition, and semantic tokens. Unlike the CLI, the LSP maintains a long-lived database that persists across requests.

#### I. State Management

The LSP server maintains:

```rust
struct RayLanguageServer {
    /// In-memory document content (unsaved edits)
    documents: HashMap<Url, DocumentData>,
    /// The query database (long-lived)
    db: Database,
    /// Workspace file graph (incrementally updated)
    snapshot: WorkspaceSnapshot,
    /// Configuration
    workspace_root: FilePath,
    toolchain_root: Option<FilePath>,
}
```

**Document overlays**: When a file is open in the editor, the LSP uses the in-memory text instead of disk content. The database's `FileSource` query checks overlays first:

```rust
fn file_source(db: &Database, file_id: FileId) -> String {
    let path = db.snapshot.file_path(file_id);
    // Check overlay first (editor's unsaved content)
    if let Some(overlay) = db.overlays.get(&path) {
        return overlay.clone();
    }
    // Fall back to disk
    std::fs::read_to_string(&path).unwrap_or_default()
}
```

**Snapshot updates**: The `WorkspaceSnapshot` is incrementally updated when files change on disk (via file watcher):

| Event | Snapshot Update |
|-------|-----------------|
| File created | Add file, update module membership, re-resolve imports that previously failed |
| File deleted | Remove file, update module membership, mark affected queries dirty |
| File renamed | Combination of delete + create |
| File modified | No snapshot change (content comes from overlay or disk read) |

#### II. Event Handling

LSP events trigger query invalidation and re-evaluation:

**`didOpen`**: Add document to overlays, publish diagnostics.

```rust
async fn did_open(&self, params: DidOpenTextDocumentParams) {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path);

    // Store overlay
    self.documents.insert(uri, DocumentData {
        text: params.text_document.text,
        version: params.text_document.version,
    });

    // Invalidate cached FileSource for this file
    self.db.invalidate::<FileSource>(file_id);

    // Re-publish diagnostics (pulls fresh parse, typecheck, etc.)
    self.publish_diagnostics(&uri).await;
}
```

**`didChange`**: Update overlay, invalidate, re-publish.

```rust
async fn did_change(&self, params: DidChangeTextDocumentParams) {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path);

    // Update overlay with new content
    if let Some(doc) = self.documents.get_mut(&uri) {
        doc.text = params.content_changes.last().unwrap().text.clone();
        doc.version = params.text_document.version;
    }

    // Invalidate FileSource → cascades to Parse → NameResolutions → etc.
    self.db.invalidate::<FileSource>(file_id);

    self.publish_diagnostics(&uri).await;
}
```

**`didClose`**: Remove overlay, file reverts to disk content.

```rust
async fn did_close(&self, params: DidCloseTextDocumentParams) {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path);

    // Remove overlay
    self.documents.remove(&uri);

    // Invalidate so next read uses disk content
    self.db.invalidate::<FileSource>(file_id);

    // Clear diagnostics for closed file
    self.client.publish_diagnostics(uri, Vec::new(), None).await;
}
```

**Invalidation cascading**: When `FileSource` is invalidated, all queries that depend on it become stale. On next access, they recompute using the red-green algorithm (same as CLI cache validation, but in-memory).

#### III. Feature Handlers

Each LSP feature maps to one or more queries:

**Diagnostics** (`textDocument/publishDiagnostics`):

```rust
async fn publish_diagnostics(&self, uri: &Url) {
    let path = uri_to_filepath(uri);
    let file_id = self.snapshot.file_id(&path)?;

    // file_diagnostics pulls parse, name_resolutions, typecheck_group
    let diagnostics = file_diagnostics(&self.db, file_id);

    let lsp_diagnostics = diagnostics
        .into_iter()
        .map(|e| to_lsp_diagnostic(e, &path))
        .collect();

    self.client.publish_diagnostics(uri.clone(), lsp_diagnostics, version).await;
}
```

**Hover** (`textDocument/hover`):

```rust
async fn hover(&self, params: HoverParams) -> Option<Hover> {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path)?;
    let position = params.position;

    // Find node at position using source map from parse
    let parsed = parse(&self.db, file_id);
    let node_id = parsed.srcmap.find_at_position(&path, position.line, position.character)?;

    // Get type for this node
    let ty = ty_of(&self.db, node_id)?;

    // Get definition info if this is a name reference
    let resolutions = name_resolutions(&self.db, file_id);
    let def_info = resolutions.get(&node_id)
        .and_then(|r| r.to_def_target())
        .map(|target| def_scheme(&self.db, target));

    Some(Hover {
        contents: format_hover(ty, def_info),
        range: parsed.span_of(node_id).map(span_to_range),
    })
}
```

**Go to Definition** (`textDocument/definition`):

```rust
async fn goto_definition(&self, params: GotoDefinitionParams) -> Option<Location> {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path)?;
    let position = params.position;

    // Find node at position
    let parsed = parse(&self.db, file_id);
    let node_id = parsed.srcmap.find_at_position(&path, position.line, position.character)?;

    // Resolve to definition via name_resolutions
    let resolutions = name_resolutions(&self.db, file_id);
    let target = resolutions.get(&node_id)?.to_def_target()?;

    // Get definition record (handles both workspace and library)
    let record = definition_record(&self.db, target);
    let location = record.source_location?;

    let (uri, range) = match location {
        SourceLocation::Workspace { file, span } => {
            (filepath_to_uri(&self.snapshot.file_path(file)), span_to_range(span))
        }
        SourceLocation::Library { filepath, span } => {
            (filepath_to_uri(&filepath), span_to_range(span))
        }
    };

    Some(Location { uri, range })
}
```

**Semantic Tokens** (`textDocument/semanticTokens/full`):

```rust
async fn semantic_tokens_full(&self, params: SemanticTokensParams) -> Option<SemanticTokens> {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path)?;

    // semantic_tokens query produces token list from AST + type info
    let tokens = semantic_tokens(&self.db, file_id);

    Some(tokens)
}
```

The `semantic_tokens` query depends on `parse` (for AST structure) and optionally typechecking (for type-aware coloring like distinguishing functions from variables).

**Completion** (`textDocument/completion`):

```rust
async fn completion(&self, params: CompletionParams) -> Option<CompletionList> {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path)?;
    let position = params.position;

    // Get completion context (kind, scope, expected type, receiver type)
    let ctx = completion_context(&self.db, file_id, position)?;

    let mut items = Vec::new();
    match ctx.kind {
        CompletionKind::Member => {
            // After `.` - complete methods/fields on receiver type
            let receiver_ty = ctx.receiver_type?;
            for (name, def_id) in methods_for_type(&self.db, receiver_ty) {
                items.push(completion_item(name, def_id, &ctx));
            }
        }
        CompletionKind::Scope => {
            // Bare identifier - complete from scope
            for (name, def_id) in ctx.scope {
                items.push(completion_item(name, def_id, &ctx));
            }
        }
        CompletionKind::ModuleMember(module_path) => {
            // After `::` on module - complete module exports
            let exports = module_def_index(&self.db, module_path);
            for (name, def_id) in exports {
                items.push(completion_item(name, def_id?, &ctx));
            }
        }
        CompletionKind::TypeMember(type_def_id) => {
            // After `::` on type - complete associated items
            for (name, def_id) in associated_items(&self.db, type_def_id) {
                items.push(completion_item(name, def_id, &ctx));
            }
        }
    }

    // Rank by type compatibility if expected_type is known
    if let Some(expected) = ctx.expected_type {
        items.sort_by_key(|item| type_compatibility_rank(&self.db, item.def_id, expected));
    }

    Some(CompletionList { is_incomplete: false, items })
}
```

Completion depends on several queries:
- `completion_context(FileId, Position)` → determines completion kind, scope, receiver type, expected type
- `expected_type_at(FileId, Position)` → infers expected type from surrounding context (function parameter, assignment, etc.)
- `scope_at(FileId, Position)` → names in scope at the cursor position
- `methods_for_type(Ty)` → available methods on a type (from impls)
- `module_def_index(ModulePath)` → exports from a module
- `associated_items(DefTarget)` → associated items for a type (constructors, static methods)

**Parser recovery requirement**: For mid-expression completion (e.g., `foo(bar.|)`), the parser must produce a partial AST that preserves:
- The incomplete member access (receiver `bar`, no member yet)
- The surrounding call expression (callee `foo`, partial arguments)
- Enough context to determine cursor position semantics

The parser must support error recovery for these scenarios. The current parser has partial recovery support; extending it for completion is part of Phase 4 (Integration) work.

**Rename** (`textDocument/rename`):

```rust
async fn rename(&self, params: RenameParams) -> Option<WorkspaceEdit> {
    let path = uri_to_filepath(&params.text_document.uri);
    let file_id = self.snapshot.file_id(&path)?;
    let position = params.position;

    // Find the definition being renamed (must be workspace definition)
    let parsed = parse(&self.db, file_id);
    let node_id = parsed.srcmap.find_at_position(&path, position.line, position.character)?;
    let resolutions = name_resolutions(&self.db, file_id);
    let target = resolutions.get(&node_id)?.to_def_target()?;

    // Can only rename workspace definitions
    let def_id = target.as_workspace()?;  // Returns None for library defs

    // Find all references to this definition (workspace-wide)
    let references = find_all_references(&self.db, &self.snapshot, target);

    // Build workspace edit
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for (ref_file_id, ref_node_id) in references {
        let ref_path = self.snapshot.file_path(ref_file_id);
        let ref_parsed = parse(&self.db, ref_file_id);
        let span = ref_parsed.span_of(ref_node_id)?;

        let uri = filepath_to_uri(&ref_path);
        changes.entry(uri).or_default().push(TextEdit {
            range: span_to_range(span),
            new_text: params.new_name.clone(),
        });
    }

    // Include the definition site itself
    let def_parsed = parse(&self.db, def_id.file);
    let def_span = def_parsed.def_header(def_id).name_span;
    let def_uri = filepath_to_uri(&self.snapshot.file_path(def_id.file));
    changes.entry(def_uri).or_default().push(TextEdit {
        range: span_to_range(def_span),
        new_text: params.new_name.clone(),
    });

    Some(WorkspaceEdit { changes: Some(changes), ..Default::default() })
}

fn find_all_references(db: &Database, snapshot: &WorkspaceSnapshot, target: DefTarget) -> Vec<(FileId, NodeId)> {
    let mut refs = Vec::new();
    // Scan all files in workspace (lazy approach)
    for file_id in snapshot.all_files() {
        let resolutions = name_resolutions(db, file_id);
        for (node_id, resolution) in resolutions {
            if resolution.to_def_target() == Some(target) {
                refs.push((file_id, node_id));
            }
        }
    }
    refs
}
```

Rename uses a lazy approach: scan all `name_resolutions` across the workspace to find references. This is simpler than maintaining an eager reverse index, though slower for large workspaces. An optimized version could build `ReferencesIndex(DefTarget) → Vec<(FileId, NodeId)>` incrementally.

#### IV. Initialization

When the LSP server starts (or a workspace is opened), it performs eager full analysis:

```rust
async fn initialize(&mut self, params: InitializeParams) -> InitializeResult {
    let root = params.root_uri.map(uri_to_filepath);
    self.workspace_root = root.clone();

    // 1. Discover workspace structure
    let snapshot = WorkspaceSnapshot::discover(&root, &self.toolchain_root);
    self.snapshot = snapshot;

    // 2. Initialize inputs
    self.db.set_input::<WorkspaceSnapshot>(snapshot.clone());
    for file_id in snapshot.all_files() {
        let path = snapshot.file_path(file_id);
        let content = std::fs::read_to_string(&path).unwrap_or_default();
        self.db.set_input::<FileSource>(file_id, content);
    }

    // 3. Load libraries
    for (module_path, lib_path) in &snapshot.libraries {
        let lib_data = RayLib::load(&lib_path)?;
        self.db.set_input::<LibraryData>(module_path.clone(), lib_data);
    }

    // 4. Initialize schema var allocator
    self.db.set_input::<SchemaVarAllocator>(Arc::new(Mutex::new(TyVarAllocator::new())));

    // Return capabilities immediately, then analyze in background
    InitializeResult { capabilities: server_capabilities(), .. }
}

async fn initialized(&mut self, _: InitializedParams) {
    // 5. Eager full analysis (with progress reporting)
    self.client.send_progress("Indexing workspace...", 0).await;

    let total = self.snapshot.all_files().len();
    for (i, file_id) in self.snapshot.all_files().enumerate() {
        // Run full analysis pipeline - results are cached
        let _ = file_diagnostics(&self.db, file_id);

        // Report progress
        let pct = ((i + 1) * 100) / total;
        self.client.send_progress("Indexing workspace...", pct).await;
    }

    self.client.send_progress_done().await;

    // 6. Publish initial diagnostics for all files
    for file_id in self.snapshot.all_files() {
        let path = self.snapshot.file_path(file_id);
        let uri = filepath_to_uri(&path);
        self.publish_diagnostics(&uri).await;
    }
}
```

**Why eager analysis**: Ray has pervasive type inference and cross-file dependencies. Lazy analysis would mean:
- First interaction with any file is slow (must analyze its dependencies)
- Diagnostics appear incrementally as files are opened
- Go-to-definition may fail if target file isn't analyzed yet

Eager analysis ensures all queries are warm when the user starts interacting. The progress indicator ("Indexing workspace...") sets expectations for the startup delay.

#### V. Persistent Cache

The LSP shares the same cache as the CLI (`<workspace>/.ray/cache/`). This means:
- `ray build` warms the cache → LSP startup is fast
- LSP analysis → next `ray build` is fast
- No redundant storage

**Cache persistence strategy**:

Relying on clean shutdown is insufficient—editors crash, get force-killed, or machines reboot. Instead, the LSP persists cache **on file save** (default):

```rust
async fn did_save(&self, params: DidSaveTextDocumentParams) {
    // Persist cache after save (analysis already ran on didChange)
    if self.db.has_unsaved_changes() {
        let cache_path = self.workspace_root.join(".ray/cache");
        let _ = self.db.persist_to_disk(&cache_path);
    }
}
```

This aligns with user intent—saving indicates a "checkpoint" worth preserving. Transient typing states don't pollute the cache.

Additionally, persist after initial workspace indexing completes.

**Configuration** (optional, in `ray.toml`):

```toml
[lsp]
# When to persist cache. Options: "on-save" (default), "periodic", "never"
cache_persist = "on-save"
# Interval for periodic mode (seconds)
cache_persist_interval = 60
```

The `periodic` option may be useful for users who rarely save explicitly (e.g., with auto-save disabled).

**On startup** (before eager analysis):

```rust
async fn initialize(&mut self, params: InitializeParams) {
    // ... workspace discovery ...

    // Load shared cache (same location as CLI)
    let cache_path = self.workspace_root.join(".ray/cache");
    if cache_path.exists() {
        self.db.load_from_disk(&cache_path)?;
    }

    // ... rest of initialization ...
}
```

**Concurrent access**:

Both CLI and LSP may access the cache simultaneously. We use **file locking** (similar to Cargo's build lock):

- **Read**: Acquire shared lock (multiple readers OK)
- **Write**: Acquire exclusive lock (blocks readers and other writers)

```rust
// .ray/cache.lock file for coordination
fn with_cache_read<T>(cache_path: &Path, f: impl FnOnce() -> T) -> T {
    let lock_path = cache_path.join("cache.lock");
    let lock_file = File::create(&lock_path)?;
    lock_file.lock_shared()?;  // Blocks if exclusive lock held
    let result = f();
    lock_file.unlock()?;
    result
}

fn with_cache_write<T>(cache_path: &Path, f: impl FnOnce() -> T) -> T {
    let lock_path = cache_path.join("cache.lock");
    let lock_file = File::create(&lock_path)?;
    lock_file.lock_exclusive()?;  // Blocks if any lock held
    let result = f();
    lock_file.unlock()?;
    result
}
```

If the CLI runs while the LSP is persisting cache, it briefly blocks with a message: "Waiting for cache lock...". This is the same behavior Cargo exhibits and developers are accustomed to it.

The alternative (optimistic reads) risks cascading inaccuracies if the CLI reads stale type information mid-persist.

**Cache validation during eager analysis**:

When `file_diagnostics(&self.db, file_id)` is called:
1. Check if cached result exists
2. If so, verify `FileSource` fingerprint (hash) matches current file content
3. If fingerprints match, reuse cached result (skip recomputation)
4. If not, recompute and cache new result

This means:
- Unchanged files → instant (cache hit)
- Modified files → recompute only affected queries
- New files → full analysis for that file only

**Cache invalidation**:

The cache file is invalidated (deleted) when:
- Ray toolchain version changes (embedded in cache metadata)
- Cache format version changes (due to query system updates)

**Size management**: Cache is bounded by file count × average result size. For large workspaces, consider LRU eviction of least-recently-accessed files, though in practice the full cache is usually acceptable (tens of MB for large projects).

## 5. Implementation Guide

This section describes a phased approach to implementing the query-based frontend. Each phase builds on the previous one, with clear deliverables and testing strategies. The new system is built separately from the current one - both systems coexist until the new one is complete and verified.

### Legacy System Audit

Before implementing the new query system, we should understand which legacy components can be reused, which need modification, and what transformations currently happen that the new system must account for.

#### Reusable Components (Minor Changes)

**Parser (`ray-core/src/parse/parser`)**:
- The parser itself is largely reusable - it produces ASTs from source text
- The `ParseOptions` structure and error recovery mechanisms can be reused as-is

*Required changes:*
```
File: ray-core/src/parse/parser/mod.rs

1. NodeId allocation: Change from namespace-scoped global counter to per-file
   sequential indexing. NodeIds become (FileId, local_index) pairs.

   - Remove: Global `NodeIdAllocator` or namespace-based allocation
   - Add: Per-parse `NodeIdAllocator` that resets for each file
   - Modify: `Parser::new()` to accept FileId and initialize local counter

2. DefId extraction: Parser must identify and record all top-level definitions
   during parsing, including methods inside impl/trait blocks.

   - Add: `DefHeader` struct with name, kind, span, signature_status
   - Add: `ParseResult.defs: Vec<DefHeader>` populated during parse
   - Modify: Parse handlers for fn/struct/trait/impl to emit DefHeaders

3. Return type: Change parser return from `ast::File` to `ParseResult` struct
   containing AST, SourceMap, DefHeaders, and parse errors.
```

**Type variable mapping (`TyCtx::map_vars`)**:
- Converts user-written type variables (e.g., `'a`) to unique schema variables
- **Fully reusable** - this is a pure transformation with no module dependencies

*Required changes:*
```
File: ray-typing/src/tyctx.rs (or extract to separate module)

1. Extract `map_vars` into a standalone pure function that takes:
   - Input types/schemes to map
   - A `&mut SchemaVarAllocator` for generating fresh vars
   - Returns mapped types plus forward/reverse var mappings

2. Remove dependency on `TyCtx` - the function should be callable without
   a full typing context.
```

**Type inference solver (`ray-typing`)**:
- The constraint tree building, term solving, goal solving, defaulting, and generalization logic is well-factored
- The `BindingGraph` and SCC computation can be reused directly

*Required changes:*
```
File: ray-typing/src/lib.rs

1. Change entry point from `check_module(ModuleInput)` to
   `check_binding_group(BindingGroupInput)`:

   - BindingGroupInput contains only definitions in the group
   - External dependencies accessed via callback/trait (not in input)
   - Returns TypecheckResult with schemes and node types for the group only

2. Remove mutation of TyCtx for storing results:

   - Currently: `check_module` mutates `tcx.node_schemes`, `tcx.node_tys`
   - New: Return all results in `TypecheckResult` struct
   - Caller (query system) stores results

File: ray-typing/src/env.rs

3. Change how external type schemes are accessed:

   - Currently: Looks up in `ModuleInput.bindings` (contains everything)
   - New: Callback `fn get_external_scheme(DefId) -> TyScheme` for deps outside group
   - This callback invokes `def_scheme` query for cross-group dependencies
```

**Source mapping (`SourceMap`)**:
- Maps NodeIds to source locations, doc comments, decorators
- Will be per-file (part of `ParseResult`) rather than accumulated globally

*Required changes:*
```
File: ray-core/src/sourcemap.rs

1. No structural changes needed - already maps NodeId → Span

2. Usage change: Create one SourceMap per file during parsing, store in
   ParseResult. No global accumulation.
```

**Closure pass (`ray-core/src/passes/closure.rs`)**:
- Already pure, just needs per-file inputs

*Required changes:*
```
File: ray-core/src/passes/closure.rs

1. Change input from merged Module to single-file AST:

   - Currently: `run_closure_pass(module: &Module<(), Decl>, ...)`
   - New: `closure_info(def: &Decl, bindings: &LocalBindings) -> ClosureInfo`

2. Change binding lookup to use LocalBindingId within the definition,
   not global BindingId across the module.
```

#### Transformations Currently in AST Lowering

The legacy `AstLowerCtx` in `ray-core/src/ast/lower.rs` performs several transformations. In the new system, these are split between the `file_ast(FileId)` query and other queries:

**Handled by `file_ast(FileId)`:**

1. **Compound assignment desugaring**: `x += 1` → `x = x + 1`
2. **Function literal to closure**: `Expr::Func` → `Expr::Closure`
3. **Curly shorthand expansion**: `Point { x }` → `Point { x: x }`
4. **Curly field ordering**: Reorder fields to match struct definition

**Handled by other queries:**

5. **Type variable resolution (`map_vars`)**: Handled by `mapped_def_types(DefId)` query. User type variables like `'a` are mapped to unique schema variables before typechecking.

6. **FQN resolution for types**: Handled by `name_resolutions(FileId)`. Type references are resolved like any other name.

7. **Signature scheme construction (`fresh_scheme`)**: Part of `def_scheme(DefId)` for annotated functions.

8. **Trait/Impl registration**: Replaced by queries `struct_def`, `trait_def`, `impl_def`, `operator_index`.

#### Components Requiring Significant Rework

**Module builder (`ray-core/src/sema/modules.rs`)**:
- Currently interleaves file discovery, parsing, and import resolution with global state
- Must be decomposed into separate pure queries

*Required changes:*
```
File: ray-core/src/sema/modules.rs

This file is largely REPLACED, not refactored. The functionality splits into:

1. Workspace discovery → `WorkspaceSnapshot` input (new code)
   - File enumeration moves to CLI/LSP initialization
   - Module structure derived from directory layout
   - No longer interleaved with parsing

2. Import resolution → `resolved_imports(FileId)` query (new code)
   - Pure function: takes parsed imports + WorkspaceSnapshot
   - Returns HashMap<ImportName, ModulePath>
   - No filesystem access, no global state

3. Library loading → `LibraryData` input (new code)
   - .raylib files loaded by CLI/LSP, set as inputs
   - Queries access via `library_data(ModulePath)`

What to delete:
- `ModuleBuilder` struct and its stateful methods
- `build()` method that interleaves everything
- Global `NameContext` accumulation during module building
```

**Name resolution (`ray-core/src/sema/resolve.rs`, `ray-core/src/transform/mod.rs`)**:
- Currently operates on merged module with global `NameContext`
- Must work per-file with explicit import/export tracking

*Required changes:*
```
File: ray-core/src/sema/resolve.rs (or new file)

1. Create per-file name resolution walker:

   - Input: Parsed AST, resolved imports, module exports (from sibling files)
   - Output: HashMap<NodeId, Resolution> (side table, not AST mutation)
   - No global NameContext - scope built locally per file

2. Resolution enum must handle:
   - Local definitions (in same file)
   - Sibling definitions (other files in same module)
   - Imported definitions (from other modules)
   - Library definitions (from .raylib)
   - Unresolved (error case)

File: ray-core/src/transform/mod.rs

3. Remove or gut `ModuleCombiner`:
   - The `combine()` function is eliminated entirely
   - Name resolution no longer happens during "combining"
   - Per-file resolution is a separate query

What to extract/keep:
- Resolution logic for individual names (reusable)
- Scope chain traversal logic (adapt to per-file)

What to delete:
- All code that assumes merged module
- Global NameContext usage
- `Module::resolve_names()` method
```

**Binding pass (`ray-core/src/passes/binding.rs`)**:
- Currently operates on merged module
- Logic is mostly sound but needs per-file + merge approach

*Required changes:*
```
File: ray-core/src/passes/binding.rs

1. Split into two phases:

   Phase A - Per-file binding extraction (new function):
   - Input: Single file's AST + name resolutions
   - Output: Set of (DefId, references: Vec<DefId>) for definitions in file
   - Pure function, no cross-file state

   Phase B - Graph merging (new function):
   - Input: Per-file binding sets for all files in module
   - Output: Complete BindingGraph with edges filtered by annotation status
   - Applies the "edge only to unannotated" rule

2. Change BindingId to DefId:
   - Legacy uses separate BindingId namespace
   - New system uses DefId directly (top-level defs are the binding units)
   - LocalBindingId for parameters/locals within a definition

3. Remove global state:
   - No mutable BindingGraph accumulation
   - Each query invocation produces fresh output
```

**AST lowering (`ray-core/src/ast/lower.rs`, `ray-core/src/transform/mod.rs`)**:
- Currently combines file merging with AST transformation
- Must separate and make transformations per-file

*Required changes:*
```
File: ray-core/src/ast/lower.rs

1. Extract pure transformation helpers (used by file_ast query):

   fn desugar_compound_assignment(expr: Expr) -> Expr
   fn expand_curly_shorthand(expr: Expr) -> Expr
   fn reorder_curly_fields(expr: Expr, field_order: &[String]) -> Expr
   fn convert_func_to_closure(expr: Expr) -> Expr

   These are pure functions that clone/transform, not mutate.

2. The `file_ast(FileId)` query orchestrates these transformations:
   - Query implementation calls helpers on each expression
   - Looks up struct field order via `struct_def(DefTarget)` query (not callback)
   - Returns new FileAst with transformed AST

3. Remove GlobalEnv mutation:
   - Currently registers structs/traits/impls in GlobalEnv during lowering
   - New: These become separate queries (`struct_def`, etc.)
   - Lowering just transforms AST, doesn't register types

File: ray-core/src/transform/mod.rs

4. Delete `ModuleCombiner` entirely:
   - No merged module concept
   - Each transformation is a separate query or helper
```

**TyCtx (`ray-typing/src/tyctx.rs`)**:
- Currently accumulates global type information
- Must become query-based with results stored in query cache

*Required changes:*
```
File: ray-typing/src/tyctx.rs

1. Remove mutable tables that accumulate across definitions:

   Delete/replace:
   - `node_schemes: HashMap<NodeId, TyScheme>` → query result
   - `node_tys: HashMap<NodeId, Ty>` → query result
   - `global_env` struct registration → separate queries

2. Keep stateless utilities:
   - Type pretty-printing
   - Type manipulation helpers
   - Constraint building helpers

3. For typechecking, create a lightweight context:

   struct TypecheckContext<'a> {
       allocator: &'a mut TyVarAllocator,
       external_schemes: &'a dyn Fn(DefId) -> TyScheme,
       // No mutable result storage
   }

   Results returned, not stored in context.
```

#### What the New System Omits

The new query system intentionally does NOT have an analogue to:

**Module combining (`transform::combine`)**:
- Legacy: Flattens multi-file modules into a single combined module
- New: Files are processed independently; module namespace is virtual (aggregated via `module_def_index`)

**Scope map construction**:
- Legacy: Builds `HashMap<Path, Vec<Scope>>` for all modules upfront
- New: Scope information is derived per-file from `resolved_imports` and `file_exports`

**Global `_ray_main` synthesis**:
- Legacy: Creates synthetic main functions for top-level statements
- New: `FileMain` DefId serves this purpose; actual codegen synthesis happens later

#### Migration Strategy Per Component

| Legacy Component | New Query | Notes |
|-----------------|-----------|-------|
| `Parser` | `parse(FileId)` | Reuse with stable NodeId scheme |
| `combine()` | N/A | Eliminated - per-file processing |
| `AstLowerCtx` | `file_ast(FileId)` | Desugaring, curly ordering |
| `map_vars` | `mapped_def_types(DefId)` | Separate query, reuse logic |
| `check_module` | `typecheck_group(BindingGroupId)` | Adapt to per-group |
| `SourceMap` | `ParseResult.source_map` | Per-file, reuse structure |
| `TyCtx` tables | Query results | `struct_def`, `trait_def`, etc. |
| `ModuleBuilder` | `WorkspaceSnapshot` + queries | See detailed changes above |
| `NameContext` | `name_resolutions(FileId)` | Per-file, no global state |
| `GlobalEnv` | `struct_def`, `trait_def`, etc. | On-demand via queries |

#### AST Transformation Query

The legacy `AstLowerCtx` transformations are handled by the `file_ast(FileId)` query, which depends on `parse(FileId)`, `name_resolutions(FileId)`, and `struct_def(DefTarget)`. See Section 3.C.II for the full specification.

Most downstream queries should depend on `file_ast`, not `parse`. The exceptions are:
- `file_imports` and `file_exports` - extract data from raw parse
- `name_resolutions` - must use raw parse to avoid circular dependency

### A. Phase 1: Query Infrastructure & Parsing

**Goal**: Establish the query system foundation and implement the simplest queries (parsing).

**Queries to implement**:
- `WorkspaceSnapshot` construction (the root input)
- `FileSource` input
- `parse(FileId)` → `ParseResult`
- `file_imports(FileId)` → `Vec<ImportPath>`
- `file_exports(FileId)` → `Vec<(String, DefId)>`

**Key implementation work**:
- Query engine: memoization, dependency tracking, fingerprinting, invalidation
- `DefId` and `NodeId` assignment during parsing
- `ParseResult` structure with `DefHeader` extraction
- `WorkspaceSnapshot` builder (file discovery, module structure)

**Testing strategy**:
- Unit tests for query memoization (same input → cached result)
- Unit tests for invalidation (change input → dependents recompute)
- Unit tests for fingerprinting (same content after edit → no invalidation)
- Parse existing test files through new system, compare AST output to current parser
- Verify `DefId` assignment is deterministic and stable across parses

**Deliverable**: Can parse a workspace via the query system and produce identical ASTs to the current system.

### B. Phase 2: Name Resolution

**Goal**: Implement per-file name resolution without merging files into a single module.

**Queries to implement**:
- `resolved_imports(FileId)` → `HashMap<String, Result<ModulePath, ImportError>>`
- `module_def_index(ModulePath)` → `HashMap<String, Result<DefId, NameCollision>>`
- `name_resolutions(FileId)` → `HashMap<NodeId, Resolution>`
- `def_for_path(ItemPath)` → `Option<DefTarget>`
- `struct_def(DefTarget)` → `StructDef`
- `trait_def(DefTarget)` → `TraitDef`
- `impl_def(DefTarget)` → `ImplDef`
- `type_alias(DefTarget)` → `TypeAliasDef`
- `impls_for_type(DefTarget)` → `ImplsForType`
- `impls_for_trait(DefTarget)` → `Vec<DefTarget>`
- `file_ast(FileId)` → `FileAst` (AST transformations, depends on `name_resolutions` and `struct_def`)

**Key implementation work**:
- Import resolution against `WorkspaceSnapshot` (no filesystem access)
- Module namespace aggregation from per-file exports
- Name resolution walker that produces `Resolution` side-table
- Cross-module reference validation (unannotated functions can't be referenced)
- AST transformation pass (compound assignment, curly desugaring/reordering)

**Testing strategy**:
- Resolve names in test files, verify `Resolution` values match expected
- Test cross-module references (valid annotated, invalid unannotated)
- Test name collisions (same name in sibling files)
- Test import errors (unknown module, ambiguous)
- Compare `name_resolutions` output against current `NameContext` behavior for existing test suite
- Test `file_ast` transformations: compound assignment, curly shorthand, curly field ordering
- Verify `file_ast` output matches legacy lowered AST for existing test files

**Deliverable**: Can resolve all names in a module without merging files. Name resolution results match current system for valid programs. AST transformations produce equivalent output to legacy lowering.

### C. Phase 3: Binding Analysis & Typechecking

**Goal**: Implement binding graph construction, SCC computation, and typechecking at binding-group granularity.

**Queries to implement**:
- `def_deps(DefId)` → `Vec<DefId>` (workspace-only)
- `binding_graph(ModulePath)` → `BindingGraph`
- `binding_groups(ModulePath)` → `Vec<BindingGroupId>`
- `binding_group_members(BindingGroupId)` → `Vec<DefId>`
- `binding_group_for_def(DefId)` → `BindingGroupId`
- `closure_info(NodeId)` → `Option<ClosureInfo>`
- `mapped_def_types(DefId)` → `MappedDefTypes`
- `typecheck_group(BindingGroupId)` → `TypecheckResult`
- `def_scheme(DefTarget)` → `TyScheme` (handles both workspace and library)
- `ty_of(NodeId)` → `Ty`
- `call_resolution(NodeId)` → `Option<CallResolution>`

**Key implementation work**:
- Binding graph construction with inference-edge filtering
- Tarjan's SCC algorithm for binding group computation
- Schema var allocation and type variable mapping (`mapped_def_types`)
- Adapt existing typechecker to work per-binding-group
- Type result storage in query results (not mutable `TyCtx`)

**Testing strategy**:
- Test SCC computation on known dependency graphs
- Test that annotated functions break inference dependencies
- Compile test programs through new system, verify inferred types match current system
- Incremental tests: edit a function body, verify only its binding group retypechecks
- Incremental tests: edit an unannotated function, verify dependents retypecheck
- Incremental tests: edit an annotated function body, verify dependents don't retypecheck

**Deliverable**: Can typecheck a module at binding-group granularity. Type schemes match current system. Incremental recomputation works correctly.

### D. Phase 4: Integration

**Goal**: Wire up CLI and LSP to use the query system, replacing the current frontend.

**Queries to implement**:
- `file_diagnostics(FileId)` → `Vec<RayError>`
- `span_of(NodeId)` → `Span`
- `find_at_position(FileId, line, col)` → `Option<NodeId>`
- `symbol_targets(NodeId)` → `Vec<SymbolTarget>`
- `def_name(DefTarget)` → `String`
- `def_path(DefTarget)` → `ItemPath`
- `definition_record(DefTarget)` → `DefinitionRecord`
- `semantic_tokens(FileId)` → `SemanticTokens`
- `scope_at(FileId, Position)` → `Vec<(String, ScopeEntry)>`
- `expected_type_at(FileId, Position)` → `Option<Ty>`
- `completion_context(FileId, Position)` → `Option<CompletionContext>`
- `methods_for_type(Ty)` → `Vec<(String, DefTarget)>`
- `associated_items(DefTarget)` → `Vec<(String, DefTarget)>`
- Operator and builtin queries

**Key implementation work**:
- CLI: `ray build` and `ray analyze` using query system
- CLI: Persistent cache implementation (`.ray/cache/`)
- LSP: State management with document overlays
- LSP: Event handlers (`didOpen`, `didChange`, `didClose`)
- LSP: Feature handlers (hover, go-to-definition, completion, rename, semantic tokens)

**Testing strategy**:
- End-to-end CLI tests: build test programs, verify output matches current system
- CLI cache tests: build, edit file, rebuild, verify cache hits/misses
- LSP integration tests: hover returns correct type info
- LSP integration tests: go-to-definition navigates to correct location
- LSP integration tests: completion returns expected items
- LSP integration tests: rename updates all references
- Performance benchmarks: LSP response time on edits

**Deliverable**: CLI and LSP fully migrated to query system. Current frontend can be removed.

## 6. Future Considerations

The following are out of scope for this design but may be considered in the future:

- **Parallelism**: Query evaluation could be parallelized, with multiple queries executing concurrently. The query system's pure-function model makes this feasible, but requires careful handling of shared caches.

- **Persistent workspace cache**: The CLI cache described in Section 4.A could be extended to cache across workspaces or shared between developers (similar to distributed build caches).

- **Finer-grained invalidation**: The current design invalidates at file granularity for early stages and definition granularity for later stages. Finer granularity (e.g., statement-level) could reduce recomputation but adds complexity.

- **Lazy typechecking**: Currently, `file_diagnostics` eagerly typechecks all definitions. For very large codebases, lazy typechecking (only typecheck definitions reachable from the current file) could improve responsiveness.

- **Incremental LIR/codegen**: This design covers the frontend (through typechecking). Extending incrementality to LIR generation and LLVM codegen is a separate effort.
