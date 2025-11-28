# ray-typing-v2 audit

This file summarizes, per module, how implementations relate to
`docs/type-system.md`. New work should either fully implement the relevant
spec rules or add an explicit `TODO` marker at the gap.

Each section below names the relevant spec sections and calls out any known
approximations.

## binding_groups.rs

- Spec: Section 3.1–3.3 (binding groups / SCCs).
- Implements `BindingId`, `BindingGroup`, `BindingGraph`, and SCC-based
  `compute_binding_groups`, matching the spec's SCC-based grouping.
- Current usage:
  - `BindingGraph::add_binding` is used in `ModuleInput` construction so that
    `binding_groups()` returns one group per binding.
  - `BindingGraph::add_edge` is **not** called anywhere yet; there is no
    dependency analysis over the Ray AST for v2, so all bindings are treated
    as independent SCCs.
- Status: the SCC machinery is implemented but not yet exercised with real
  dependency edges; wiring edge construction from the frontend will be
  required to fully realize Section 3.1–3.3.

## constraints.rs

- Spec: Section 2 (constraint language).
- Defines `ConstraintKind::{Eq, Class, HasField, Recv}` and `Constraint` with
  `TypeSystemInfo`, aligned with the predicate kinds in the spec
  (equality, class predicates, `HasField`, `Recv`).
- Status: complete for the predicates described so far; additional predicate
  forms must be added explicitly if the spec expands.

## context.rs

- Spec: Section 4 (constraint generation) and Appendix A (expression forms).
- `ExprKind` and `Pattern` are a reduced IR used for constraint generation and
  type context, corresponding to the expression/pattern forms covered in:
  - A.1 literals
  - A.2 operators
  - A.3 records/field access and indexing
  - A.6 control flow
  - A.8 assignment
- Known gaps:
  - `AssignLhs` only has `Binding(BindingId)`; deref/field/index/destructuring
    LHS forms from A.8 are not yet represented.
- Status: intentional subset of the spec; unmodeled expression/pattern forms
  must either be rejected in lowering or added to `ExprKind`/`AssignLhs` with
  matching constraint rules.

## constraint_tree.rs

- Spec: Section 4 (constraint generation) and Appendix A.
- `build_constraint_tree_for_group`:
  - One child node per binding group element.
  - Introduces a mono type for the binding and an equality tying it to the
    binding's body (Section 4.3).
- `generate_constraints_for_expr` implements:
  - Literals (A.1): `LiteralInt` → `Int[T]`, `LiteralFloat` → `Float[T]`,
    `LiteralBool`/`Nil` → equality to `bool`/`nilable[?]`.
  - Variable references (4.3): instantiate binding schemes and equate with
    expression type.
  - Struct literals and field access (4.5, A.3): `HasField` predicates and
    nominal struct type equalities.
  - Pointers (Section 1.1): `Boxed`, `Ref`, `Deref`.
  - Tuples (1.2).
  - Indexing (A.3): `Index[Container, Index, Elem]` predicate.
  - Operators (A.2): `BinaryOp` and `UnaryOp` to operator traits.
  - Nilable and pattern guards (Pattern-if/while, Section A.6).
  - Control flow (A.6): `If`, `While`, `WhilePattern`, `Loop`, `Break`,
    `Continue`, `Return`, `For`.
  - Calls (4.4): callee type `== (arg_tys...) -> result_ty`.
- Known gaps:
  - Comment at `generate_constraints_for_group` still calls the tree "stubbed";
    the per-expression rules are implemented, but full-scoped environments and
    additional givens (e.g. from nested scopes) may need extension as the spec
    evolves.
- Status: expression-level constraints for the current `ExprKind` set are in
  place; when new expression forms are added to `ExprKind`, they must be added
  here as well.

## defaulting.rs

- Spec: Section 8.2–8.3 (defaultable predicates and defaulting algorithm).
- `apply_defaulting`:
  - Uses `find_defaultable_classes` to select flexible type-variable classes
    `α` that appear as receivers in residual `Class` predicates whose traits
    declare `default(T_default)` (Section 8.2).
  - `group_predicates_by_class` clusters residual predicates by `α`
    (Section 8.2 "Clustering by mentions of α").
  - For each `α`:
    - Skips non-flexible classes via `is_flexible`.
    - Skips classes that will be generalized for some value binding in the
      current group using `will_be_generalized` (Section 8.2, 3.4).
    - Collects candidate defaults from `default_candidates_for`, which looks
      up trait-level `default(T)` markers on `TraitTy`.
    - For each candidate `T_default`, uses `unify` and
      `solve_predicates_for_class` to test viability against the cluster
      `preds_alpha` (Section 8.3).
    - Commits unique viable defaults and records decisions in
      `DefaultingLog` (`DefaultingOutcomeKind` mirrors the spec's outcome
      cases).
  - Applies the final `Subst` to returned residual constraints so later phases
    see the simplified residuals.
- `will_be_generalized`:
  - Takes `ModuleInput`, `BindingGroup`, `TypeContext`, and `Subst`.
  - For each binding in the group:
    - Uses a local `is_syntactic_value_expr` (same heuristic as in
      `generalize.rs`) to approximate `eligible_for_generalization` from
      Section 3.4.
    - If the binding is a syntactic value and `α` occurs as a free meta in its
      solved type, returns `true`, causing defaulting to reject `α` as `Poly`.
- Known approximations:
  - `is_syntactic_value_expr` currently only recognizes literals, `some(v)`,
    and struct literals with value fields. Function/closure literals and other
    value forms must be added here once they are present in `ExprKind`.
- Status: defaulting follows Section 8's algorithm, with an explicit,
  binding-group-aware `will_be_generalized` check; any new value forms must
  extend `is_syntactic_value_expr`.

## generalize.rs

- Spec: Section 3.4 (generalization, value restriction).
- `generalize_group`:
  - Inputs: `ModuleInput`, `TypeContext`, `BindingGroup`, residual constraints,
    final `Subst`.
  - Computes `vars_in_residuals` from residual constraints so metas that still
    appear in residual predicates are treated as non-generalizable (Section
    3.4 "will be generalized" vs residuals).
  - For each binding in the group:
    - Uses `is_syntactic_value_expr` to enforce the value restriction from
      Section 3.4 (`is_syntactic_value`).
    - Applies `subst` to the scheme's type to get the solved mono type.
    - If any free meta appears in `vars_in_residuals` or the RHS is not a
      syntactic value, keeps the binding monomorphic (`TyScheme::mono`).
    - Otherwise, collects remaining meta variables, renames them to fresh
      schema variables `?sN`, applies a closing substitution to the scheme
      body, and returns the quantified `TyScheme`.
- Known approximations:
  - `is_syntactic_value_expr` uses the same literal/struct heuristic as
    defaulting and will need to be extended when function/closure literals are
    added to `ExprKind`.
  - Distinguishing annotated bindings (explicit schemes) from inferred
    bindings is not yet wired; once that metadata is available, such bindings
    should be excluded from generalization.
- Status: generalization matches the spec's algorithm for current value forms
  and residual handling; new value forms and binding annotations must be
  integrated explicitly.

## goal_solver.rs

- Spec: Section 5.2–5.3 (goal solving, instances, HasField, Recv).
- `solve_goals`:
  - Applies substitution to the constraint tree, then walks it with
    `solve_node` to discharge predicates bottom-up, collecting residuals and
    type errors (unsolved predicates) as per Section 5.2.
- `solve_constraints`:
  - Uses `solve_with_givens` for class predicates against givens.
  - Uses `solve_with_instances` for class predicates against `ImplTy` from
    `GlobalEnv`.
  - Uses `solve_has_field` for `HasField` based on `StructTy` metadata.
  - Uses `solve_recv` for `Recv` via auto-ref/deref BFS (Section 5.3).
- Status: implements the core given/wanted pipeline described in the spec for
  the current `ConstraintKind` variants; additional predicate kinds must be
  added here consciously.

## info.rs

- Spec: Section 9 (TypeSystemInfo and error reporting).
- `Info` and `TypeSystemInfo`:
  - Represent equality type pairs, unsolved and ambiguous predicates, and
    detail strings, and support substitution over their payloads.
- Status: integrated into constraints, solvers, and errors; no hidden gaps.

## instances.rs

- Spec: Sections 2.2 and 6 (trait instances, operator traits).
- `GlobalEnv`:
  - Stores `StructTy`, `TraitTy`, `ImplTy`, and operator tables for both infix
    and prefix operators.
  - Provides `get_struct`, `get_trait`, and `iter_impls` used by goal solving.
- Known TODO:
  - Where-clause predicates on impls are not represented; the spec's richer
    instance contexts will require adding predicate lists to `ImplTy` and
    threading them through goal solving.
- Status: supports the current operator and instance use cases; where-clauses
  are explicitly called out in `types.rs`.

## lib.rs

- Spec: Sections 3–5, 8–9 (pipeline structure).
- `check_module` / `check_binding_group` implement the per-group pipeline:
  - Build constraint tree (Section 4).
  - Solve equalities (Section 5.1).
  - Solve predicates (Section 5.2).
  - Apply defaulting (Section 8).
  - Generalize bindings (Section 3.4).
  - Aggregate errors (Section 9).
- Tests:
  - End-to-end tests for literals, control flow, pattern-if, loops, and
    struct field access.
- Status: pipeline matches the spec; further gaps are localized to the phase
  modules above and are documented there.

## term_solver.rs

- Spec: Section 5.1 (term solving).
- `solve_equalities`:
  - Collects equality constraints from the tree, calls `unify`, and applies
    the evolving substitution back to the tree so later phases see simplified
    types.
- Status: equality handling matches the spec's description for the current
  `Ty` constructors.

## types.rs

- Spec: Sections 1–2 (type language, traits).
- `Ty`, `TyVar`, `TyScheme`:
  - Represent the core types from Section 1 (primitives, pointers, tuples,
    arrays, nilable via `Proj`, top/bottom).
- `StructTy`, `TraitTy`, `ImplTy`:
  - Nominal metadata for records, traits, and impls; `TraitTy.default_ty`
    corresponds to `default(T)` in Section 8.2.
- Known TODO:
  - `ImplTy` includes a comment about where-clause predicates not yet wired;
    these must be added when the predicate language is extended to cover
    impl contexts more fully (Sections 2.2 and 6).
- Status: base type and nominal metadata representation matches the parts of
  the spec in use today; any extension of the type language should be
  mirrored here and in `unify.rs`.

## unify.rs

- Spec: Section 5.1 (unification).
- `unify`:
  - Handles `never`, `any`, `Const`, `Var`, `Func`, `Ref`, `RawPtr`, `Proj`,
    `Tuple`, and `Array` with:
    - Occurs check via `occurs_in`.
    - Rigid/meta distinction via `TyVar::is_meta` and `bind_var`.
    - Error reporting through `TypeError`.
- Status: unifier is complete for the current `Ty` variants; new variants must
  be added here explicitly as the type language grows.

---

## Spec coverage by section (rough)

Percentages below are rough, qualitative estimates of how much of each spec
section is currently implemented in `ray-typing-v2`. They are intended to
highlight gaps, not to serve as precise metrics.

### Section 1: Types

- Rough completeness: ~80%.
- Implemented:
  - Core types in `Ty` (primitives, pointers, tuples, arrays, nilable via
    `Proj`, `any`, `never`) and their unification rules.
  - Free type variable tracking and substitution.
- Missing / simplified:
  - Any additional type constructors beyond what is represented in `Ty`.
  - Refinements around pointer flavors and any future effect/ownership types.

### Section 2: Predicates and traits

- Rough completeness: ~75%.
- Implemented:
  - `ConstraintKind::{Eq, Class, HasField, Recv}` and corresponding solver
    support in `goal_solver.rs`.
  - `TraitTy` and `ImplTy` metadata, including `default(T)` on traits.
- Missing / simplified:
  - Where-clause predicates on impls (only noted as TODO in `ImplTy`).
  - Any richer predicate forms beyond the current four kinds.

### Section 3: Bindings, schemes, generalization

- Rough completeness: ~80%.
- Implemented:
  - Binding groups via SCCs (`BindingGraph`).
  - Binding schemes via `TyScheme` and `binding_schemes` in `TypeContext`.
  - Generalization pass (`generalize_group`) that is value-restricted and
    residual-aware, with meta → schema renaming.
- Missing / simplified:
  - Distinguishing explicitly annotated bindings from inferred ones in
    generalization.
  - Complete coverage of all syntactic value forms in `is_syntactic_value`.

### Section 4: Constraint generation

- Rough completeness: ~70%.
- Implemented:
  - Constraint-tree construction per binding group.
  - Expression-level rules for the current `ExprKind` set (literals, vars,
    struct literals/field access, pointers, tuples, indexing, operators,
    pattern-if/while, for/while/loop/break/continue/return, calls).
- Missing / simplified:
  - Some expression forms present in the frontend but not yet represented in
    `ExprKind` (e.g. casts, more complex patterns) are not covered here.
  - Environment/givens modeling is minimal and may need refinement for more
    advanced scenarios.

### Section 5: Solvers (term and goal)

- Rough completeness: ~80%.
- Implemented:
  - Term solver over equality constraints (`term_solver.rs`) using `unify`.
  - Goal solver over predicates (`goal_solver.rs`) with givens, instances,
    `HasField`, and `Recv`.
- Missing / simplified:
  - Any advanced instance resolution strategies (overlaps, coherence) are not
    modeled; the current search is straightforward.
  - No explicit evidence objects yet; predicates are recorded only via
    residuals and errors.

### Section 6: Instance resolution

- Rough completeness: ~70%.
- Implemented:
  - GlobalEnv instances (`ImplTy`) and trait metadata (`TraitTy`).
  - Class predicate resolution against instances in `solve_with_instances`.
- Missing / simplified:
  - Where-clause contexts on instances are not represented or used in solving.
  - Super-trait relationships are stored but not yet fully exploited in goal
    solving.

### Section 7: Multi-Parameter Type Classes

- Rough completeness: ~40%.
- Implemented / respected:
  - Receiver-first convention: class predicates always treat the first
    argument as the receiver (`RecvTy`) and additional arguments as plain
    parameters.
  - No functional dependencies or inference from trait definitions alone:
    `solve_with_instances` and `solve_with_givens` only derive equalities by
    unifying predicate heads at use sites, not from trait declarations.
  - Local improvement: equalities learned from givens are applied via the
    unifier in the current solving context; there is no global fundep-like
    behavior.
- Missing / simplified:
  - Ambiguity handling for multi-parameter traits: when multiple impls are
    viable, Section 7.3 expects the solver to treat this as ambiguity rather
    than silently picking one. `solve_with_instances` currently commits to the
    first successful impl and does not detect/report such ambiguity (see the
    TODO comment there).
  - No explicit evidence objects for improvement; equalities are reflected
    only via the substitution.

### Section 8: Defaulting

- Rough completeness: ~85%.
- Implemented:
  - Detection of defaultable classes from residuals and trait defaults.
  - Clustering of predicates per type-variable class.
  - Candidate testing via unification and local goal-solver runs.
  - `will_be_generalized` check integrated with the actual binding group and
    syntactic value predicate.
  - Application of final substitution to residuals.
- Missing / simplified:
  - `is_syntactic_value_expr` still only covers literals, `some(v)`, and
    struct-literal values; more value forms must be added as the IR evolves.

### Section 9: Errors and diagnostics

- Rough completeness: ~70%.
- Implemented:
  - `TypeSystemInfo` and `Info` used to annotate constraints and errors.
  - Equality and predicate failures enriched with contextual info in the term
    solver and goal solver.
- Missing / simplified:
  - Some error sites still construct relatively bare `TypeSystemInfo`.
  - No dedicated evidence threading yet; later phases consume only types and
    residual predicates, not richer evidence structures.

### Appendix A: Expression forms

- Rough completeness: ~70% overall.
- A.1 Literals:
  - Implemented for numeric/bool/nil; string/char/byte literals are not yet
    lowered.
- A.2 Operators:
  - Operator traits and constraints implemented via `BinaryOp`/`UnaryOp` and
    `GlobalEnv` operator tables.
- A.3 Records and indexing:
  - Struct literals and `HasField` constraints implemented; full pattern
    records are not yet modeled.
  - Indexing and index assignment depend on the `Index` class; basic read
    indexing is present.
- A.6 Control flow:
  - If/while/loop/for/break/continue/return implemented at the constraint
    level for the current IR.
  - Some frontend forms (e.g. pattern expressions outside guards) are not yet
    lowered into `ExprKind`.
- A.8 Assignment:
  - Simple `x = e` assignment is represented (`AssignLhs::Binding`) and
    generates constraints/generalization as per the spec.
  - Deref assignment `*p = e` and simple field assignment `recv.field = e`
    (with `recv` a variable) are represented via `AssignLhs::Deref` and
    `AssignLhs::Field` and have corresponding constraints.
  - Index assignment and destructuring patterns are not yet represented and
    will need explicit support in `AssignLhs`, lowering, and constraints.
- A.9 Cast expressions:
  - Casts are not yet lowered into `ExprKind` or given typing rules; Section
    A.9 is unimplemented for now.
