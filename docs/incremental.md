# Design:
## 1. Query-Based Architecture (à la rust-analyzer/Salsa)

Instead of phases, model the entire compiler as a **database of queries** with automatic memoization and dependency tracking.

```rust
// Instead of phases, you have queries:
#[query]
fn parse_file(db: &dyn CompilerDb, file: FileId) -> Arc<ParseTree>

#[query]
fn lower_ast(db: &dyn CompilerDb, file: FileId) -> Arc<HIR>

#[query]
fn infer_types(db: &dyn CompilerDb, def: DefId) -> TypeInferenceResult

#[query]
fn diagnostics(db: &dyn CompilerDb, file: FileId) -> Vec<Diagnostic>
```

**Benefits:**
- Framework handles caching, invalidation, and cycle detection automatically
- Natural composability—queries call other queries
- Finer granularity—query per function/definition instead of per file
- Demand-driven—only compute what's actually needed
- Incremental is built-in from day one, not retrofitted

## 2. Multiple IR Levels with Clear Boundaries

Instead of one AST with progressive annotations:

**Syntax Level (CST/Green Tree)**
- Concrete syntax tree with all trivia (whitespace, comments)
- Immutable, persistent data structure (red-green tree pattern)
- Lossless—can reconstruct original source exactly
- Used for: formatting, syntax highlighting, basic navigation

**High-Level IR (HIR)**
- Desugared, name-resolved, but not yet typed
- Path-based references (still symbolic)
- Source location tracking for errors
- Used for: name resolution, import analysis, IDE navigation

**Middle IR (MIR)**
- Fully typed, explicit about control flow
- DefId-based references (resolved to definitions)
- Simplified—no more syntactic sugar
- Used for: type checking, borrow checking equivalent, optimization passes

**Low-Level IR (LIR/WASM-like)**
- Ready for codegen
- All abstractions lowered (closures → environments, traits → vtables)
- Used for: final optimizations, WASM emission

**Benefits:**
- Each level has the right abstraction for its purpose
- Clear boundaries prevent accidental coupling
- Can cache at each level independently
- Easier to reason about what information is available where

## 3. Separation of Syntax and Semantic Trees

**Current problem:** Annotating AST nodes with semantic info couples syntax to semantics, making caching harder.

**Better approach:**
- Syntax tree is immutable and purely structural
- Semantic data stored in **side tables** indexed by NodeId or DefId
- Type information: `Map<ExprId, Type>`
- Name resolution: `Map<NameRef, DefId>`
- Diagnostics: `Vec<Diagnostic>` with source spans

**Benefits:**
- Can keep syntax tree across edits (red-green trees)
- Can invalidate semantic info without reparsing
- Multiple semantic analyses can coexist without interfering
- Better memory locality for specific analyses

## 4. Definition-Level Granularity

Instead of per-file phases, work at the **definition level** (functions, types, constants).

```
File A:
  fn foo() { ... }  ← Can typecheck independently
  fn bar() { ... }  ← Can typecheck independently
  
File B:
  fn baz() { ... }  ← Only depends on foo's *signature*, not body
```

**Benefits:**
- Changing a function body doesn't invalidate other functions
- True incremental compilation—only recheck changed functions
- Better parallelism—typecheck all functions in parallel after name resolution
- More responsive LSP—can show results for some functions while others are still computing

## 5. Lazy, Fault-Tolerant Evaluation

**Resilient parsing:**
- Parser produces partial AST even with errors
- Error nodes in tree instead of failing entire file
- Continue analyzing what's valid

**Lazy constraint solving:**
- Don't solve all constraints eagerly
- For LSP, solve constraints only for the function being edited
- Background: solve constraints for everything else
- Store partial solutions when full solving fails

**Uncertain/partial information:**
- Allow "unknown" as a valid state: `Type::Unknown`
- Propagate but don't error on unknowns immediately
- Provides some IDE features even in broken code

**Benefits:**
- LSP remains useful even in invalid code states
- Better error recovery and error messages
- Can provide completions, go-to-definition even with type errors

## 6. Explicit Dependency Tracking

Instead of implicit phase dependencies, make all dependencies explicit in the type system:

```rust
// Query declares what it needs
fn typecheck_function(
    db: &dyn CompilerDb,
    func: FunctionId,
    // Explicit dependencies:
    signature: &FunctionSignature,
    body_hir: &HIR,
    closure_info: &ClosureInfo,
    imported_signatures: &[Signature]
) -> TypeckResult
```

**Benefits:**
- Clear what each analysis actually needs
- Easier to parallelize (explicit dependency graph)
- Can provide partial results with subset of dependencies
- Better testability (can mock dependencies)

## 7. Streaming & Incremental Parsing

Instead of parse entire file → analyze:

**Incremental parsing:**
- Reuse unchanged subtrees from previous parse
- Only re-parse edited regions + affected parents
- Syntax error recovery to handle partial edits

**Streaming where possible:**
- Don't wait for entire file to parse before starting name resolution
- Pipeline: as each top-level definition parses, start analyzing it

**Benefits:**
- Sub-millisecond response to edits in large files
- Better for LSP interactivity
- Lower memory pressure (don't hold everything in memory)

## 8. Semantic Tokens, Not Syntax Tokens

For IDE features, compute at semantic level:

**Current:** Syntax highlighting uses parser tokens
**Better:** Semantic highlighting uses name resolution

```
my_variable  →  [local variable]
MyType       →  [type definition]
some_func    →  [function, from imported module X]
```

**Benefits:**
- Accurate highlighting even in macros
- Can show "unused variable" with different color
- Can distinguish between different kinds of references

## 9. Salience-Based Computation Prioritization

**LSP should prioritize:**
1. Currently visible file and cursor location
2. Recently modified files  
3. Files imported by visible files
4. Everything else (background)

**With query system:**
```rust
db.set_priority(current_file, Priority::High);
db.set_priority(recently_modified, Priority::Medium);
// Background thread works through Low priority queries
```

**Benefits:**
- User always sees results for what they're working on
- Complete project analysis happens eventually
- Doesn't block on errors in distant files

## 10. Separate Analysis from Artifacts

**Currently:** Each phase mutates or annotates existing data

**Better:** Pure transformations
```rust
parse: Text → CST
lower: CST → HIR
resolve: HIR → HIR + NameTable
typecheck: HIR + NameTable → TypeTable + Errors
```

All are pure functions. State lives in the database/cache layer.

**Benefits:**
- Trivial to test (no global state)
- Trivial to parallelize (no mutation)
- Trivial to cache (referential transparency)
- Can run multiple analyses simultaneously

## 11. First-Class Support for Partial Programs

Design every phase to work on **partial** programs:

- Missing imports? Fill in with `Unknown`
- Can't resolve name? Mark as `Unresolved` but continue
- Type error? Store `TypeError` but infer rest of function
- Missing definition? Use placeholder

**Benefits:**
- Work-in-progress code doesn't break entire pipeline
- Can provide IDE features while actively typing
- Better developer experience—feedback without compilation succeeding

## Architecture Sketch

```
┌─────────────────────────────────────────────┐
│  Query Database                             │
│  - Automatic memoization                    │
│  - Dependency tracking                      │
│  - Incremental invalidation                 │
└─────────────────────────────────────────────┘
                    ↓
        ┌──────────────────────┐
        │  Syntax Queries      │
        │  - parse_file        │
        │  - file_cst          │
        └──────────────────────┘
                    ↓
        ┌──────────────────────┐
        │  HIR Queries         │
        │  - file_hir          │
        │  - def_hir           │
        └──────────────────────┘
                    ↓
        ┌──────────────────────┐
        │  Resolution Queries  │
        │  - resolve_name      │
        │  - def_signature     │
        └──────────────────────┘
                    ↓
        ┌──────────────────────┐
        │  Type Queries        │
        │  - infer_def         │
        │  - check_expr        │
        └──────────────────────┘
                    ↓
        ┌──────────────────────┐
        │  Diagnostic Queries  │
        │  - file_diagnostics  │
        │  - def_diagnostics   │
        └──────────────────────┘
```

## The Big Wins

1. **Incremental by default** - Never think about caching again
2. **Responsive** - Only compute what's needed, when it's needed
3. **Parallel** - Query system can automatically parallelize
4. **Fault-tolerant** - Partial results are first-class
5. **Testable** - Pure queries are easy to unit test
6. **Extensible** - Add new queries without modifying existing ones
7. **Observable** - Query system can log/profile all computations

# Addendum: Ray-Specific Query Architecture (Salsa-Lite)

This addendum maps the general query-based approach to Ray's current architecture. It acknowledges that Ray does not currently have CST/HIR/MIR layers and focuses on queries over the existing AST plus side tables. The goal is to move toward purity and incrementalism without a disruptive rewrite.

## Query Set (Initial)
The following queries are the agreed-upon spine. Some are file-granular now, with a path to finer granularity later.

```rust
#[query]
fn parse(file: FileId) -> ParseOutput

#[query]
fn imports(file: FileId) -> ImportOutput

#[query]
fn name_resolve_decls(file: FileId) -> NameResolutionOutput

#[query]
fn name_resolve_bodies(file: FileId) -> NameResolutionOutput

#[query]
fn lower(file: FileId) -> LoweredOutput

#[query]
fn binding_analysis(file: FileId) -> BindingOutput

#[query]
fn closure_analysis(file: FileId) -> ClosureOutput

#[query]
fn typecheck_group(group: BindingGroupId) -> TypecheckOutput

#[query]
fn typecheck_file(file: FileId) -> TypecheckFileOutput
```

Notes:
- `typecheck_group` is the primary unit of typechecking; `typecheck_file` aggregates results for all groups that touch the file.
- `typecheck_group` aligns with `binding_groups` and the SCC-based design already in `ray-typing`.
- The queries above can remain file-granular while the compiler evolves toward definition-level granularity.
- Diagnostics are produced per query and aggregated by a dedicated diagnostics query.

## Binding Groups as the Typechecking Unit
Ray's type system is built around binding groups (SCCs). Instead of per-decl or per-file typechecking, the query system should treat each binding group as the unit of inference and constraint solving.

```rust
#[query]
fn binding_groups(file: FileId) -> Vec<BindingGroupId>

#[query]
fn typecheck_group(group: BindingGroupId) -> TypecheckOutput
```

Implementation notes:
- `binding_groups` can be computed from `binding_analysis(file)` by building a dependency graph over binding IDs and computing SCCs.
- `BindingGroupId` is derived from the sorted binding IDs in the group (for example, hashing the ordered list), which requires stable binding IDs.
- `typecheck_file(file)` returns the union of typechecking results for any group that includes bindings sourced from `file`.

## AST, Mutability, and Purity
Ray currently uses in-place passes (name resolution, lowering). To move toward query purity without rewriting the passes:

- `parse(file)` returns the immutable AST plus parse diagnostics.
- `name_resolve_*` and `lower` may clone the AST before mutating it, so each query returns its own artifact without mutating shared state.
- Alternatively, name resolution can return a side table (`NameTable`) keyed by `NodeId`, while leaving AST structure untouched.
- Cloning is acceptable as a first step; a later optimization can replace cloning with side tables or persistent structures.

## Mutable Global State Bridge
The backend currently relies on mutable `NameContext` and `TyCtx`. A transitional approach is to hide those behind traits so queries can pass abstract contexts while preserving existing APIs.

```rust
pub trait NameContextApi {
    fn resolve(&mut self, name: &Name) -> Option<Path>;
    fn insert(&mut self, path: Path, symbol: Symbol);
}

pub trait TypeContextApi {
    fn lookup(&self, path: &Path) -> Option<TypeId>;
    fn insert(&mut self, id: TypeId, ty: Ty);
}
```

Short term:
- Queries take `&mut impl NameContextApi` and `&mut impl TypeContextApi`.
- The query engine stores per-query outputs and applies deltas to shared contexts in a controlled place.

Longer term:
- Replace shared mutation with pure outputs (side tables keyed by IDs) and make queries referentially transparent.

## Invalidation Model (Initial)
- File content hash is the primary input key for `parse(file)` and downstream queries.
- Module discovery and import resolution can be separate queries, keyed by filesystem state and import lists.
- Finer-grained keys (definition-level hashes) can be introduced later without changing the query signatures.

## Error Boundaries and Partial Results
- Best-effort within a file when a partial AST exists; downstream stages for that file are skipped only when a prerequisite pass for that file fails.
- Other files continue to run even when a file fails a stage.
- Queries return partial outputs alongside errors when possible, especially for LSP use.

## Open Questions
- Roll-forward details for shared contexts (`NameContext`, `TyCtx`): exact delta format, application order, and whether any rollback or rebuild is needed for consistency.

## Outstanding Design Issue: Stable IDs
- Binding group stability depends on stable `BindingId` across edits.
- Mapping `BindingId` from `NodeId` is only viable if `NodeId` is stable.
- Span-based hashes are not stable: a single edit shifts spans and invalidates IDs downstream.
- Use a per-declaration namespace keyed by the top-level declaration `Path` (FQN). Binding groups only depend on top-level bindings, so stable per-decl namespaces are sufficient.
- Assumption: node ID counters within a declaration are deterministic enough to support per-node type caches.

# Implementation Guide: Query-Based Incremental Compiler
## High-Level Roadmap

### Phase 0: Foundation & Infrastructure

- Set up query system/database infrastructure
- Design core data structures (IDs, spans, interning)
- Establish file system interface and change detection
- Create testing harness

### Phase 1: Syntax Layer

- Implement incremental parser with error recovery
- Build immutable syntax tree (CST/Green tree)
- Add source mapping and span tracking
- Create syntax-level queries

### Phase 2: Name Resolution Layer

- Extract imports and build dependency graph
- Implement name resolution with query-based lookups
- Build symbol tables and cross-file indexes
- Handle scoping and visibility rules

### Phase 3: HIR (High-Level IR) Layer

- Desugar and lower AST to HIR
- Implement definition-level granularity
- Build binding and closure analysis
- Create HIR queries

### Phase 4: Type System Layer

Implement constraint generation per definition
Build constraint solver with caching
Handle cross-definition type dependencies
Generate type diagnostics

### Phase 5: CLI Integration

- Implement batch compilation entry point
- Add parallel query evaluation
- Create build caching and invalidation
- Implement watch mode

### Phase 6: LSP Integration

- Implement LSP server protocol handlers
- Add priority-based query scheduling
- Implement IDE features (hover, completion, etc.)
- Add real-time diagnostics

### Phase 7: Optimization & Polish

- Add optimization passes as queries
- Implement query profiling and debugging
- Tune caching strategies
- Performance optimization
