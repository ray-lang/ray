# Ray v2 Type System – Spec Coverage Matrix

Legend:

- `[x]` implemented and roughly spec-aligned
- `[~]` partially implemented / edge cases missing
- `[ ]` not implemented yet

Columns:

- `Lowering`: `crates/ray-core/src/typing_v2.rs`
- `Constraints`: `crates/ray-typing-v2/src/constraint_tree.rs`
- `Goals`: `crates/ray-typing-v2/src/goal_solver.rs`
- `Unify`: `crates/ray-typing-v2/src/unify.rs`
- `Defaulting`: `crates/ray-typing-v2/src/defaulting.rs`
- `Generalize`: `crates/ray-typing-v2/src/generalize.rs`
- `Errors/Info`: `crates/ray-typing-v2/src/info.rs`, `TypeError`

This is intentionally a living document; rows should be updated as code evolves.

## Section 1–2: Types, predicates, traits

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Core primitive types (`int`, `float`, `bool`) | 1.1          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | Literals, class preds `Int`/`Float`. |
| Pointer types (`*T`, raw pointers)        | 1.1          | [x]      | [x]        | [~]   | [~]   | N/A        | [x]        | [ ]         | Boxed/Ref/Deref, Recv search. |
| Tuples                                    | 1.2          | [x]      | [x]        | [~]   | [~]   | N/A        | [x]        | [ ]         | Tuple literal typing. |
| Nilable types `nilable[T]`                | 1.3          | [x]      | [x]        | [~]   | [~]   | N/A        | [x]        | [ ]         | `Some`, `Nil`, pattern guards. |
| Trait predicates (`Class`, `HasField`, `Recv`, `Index`) | 2.2 | [x] | [x] | [x] | [~] | N/A | [x] | [~] | ConstraintKind variants and solver hooks. |

## Section 3: Bindings, schemes, generalization

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Binding groups (value bindings)           | 3.1–3.3      | [~]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | BindingGraph skeleton, per-binding root nodes. |
| Type schemes on bindings (`TyScheme`)     | 3.3          | [~]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | `binding_schemes`, instantiation and generalized schemes. |
| Generalization (`forall`, value restriction) | 3.4        | [~]      | [~]        | [~]   | [x]   | N/A        | [x]        | [ ]         | Generalization implemented with residual and value checks. |

## Section 4: Constraint generation

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Variable references / schemes             | 4.3          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | Local vs global bindings, instantiation and generalized schemes. |
| Struct literals and field access          | 4.5          | [~]      | [x]        | [x]   | [x]   | [ ]        | N/A        | [~]         | No shorthand fields yet. |
| Calls and function application            | 4.4          | [x]      | [~]        | [x]   | [x]   | [ ]        | N/A        | [~]         | Constraints for callee/args incomplete. |
| Control-flow constraints (if/while/loop/for/return/break/continue) | 4.6, A.6 | [~] | [~] | [x] | [x] | [ ] | N/A | [~] | Basic rules sketched; some edges TODO. |

## Section 5: Instances and goal solving

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Given/wanted handling over constraint tree| 5.2          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | `solve_node`, `solve_constraints`; generalized schemes at roots. |
| Class predicates via instances            | 5.2          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | `solve_with_instances`. |
| HasField resolution from struct metadata  | 5.2          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | `solve_has_field`. |
| Recv auto-ref/deref search                | 5.3          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | BFS search over `T`, `*T`, `rawptr[T]`. |

## Section 8: Defaulting

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Defaultable class detection               | 8.2          | [x]      | [x]        | [x]   | [x]   | [x]        | [x]        | [~]         | `find_defaultable_classes`. |
| Predicate clustering per type-variable class | 8.2       | [x]      | [x]        | [x]   | [x]   | [x]        | [x]        | [~]         | `group_predicates_by_class`. |
| Candidate selection from trait defaults   | 8.2          | [x]      | [x]        | [x]   | [x]   | [x]        | [x]        | [~]         | `default_candidates_for`. |
| `will_be_generalized` check               | 8.3          | [ ]      | [ ]        | [ ]   | [ ]   | [ ]        | N/A        | [ ]         | TODO stub in `defaulting.rs`. |
| Local re-solve of clusters                | 8.2          | [x]      | [x]        | [x]   | [x]   | [x]        | N/A        | [~]         | `solve_predicates_for_class`. |

## Section 9: Errors and TypeSystemInfo

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Per-constraint `TypeSystemInfo`           | 9            | [x]      | [x]        | [x]   | [~]   | N/A        | [x]        | [~]         | `Constraint` carries `info`; some sites still create empty info. |
| Attaching source spans to constraints     | 9            | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | Uses `expr_src`; may need richer context. |
| Threading info into `TypeError`           | 9            | [x]      | [x]        | [x]   | [~]   | N/A        | [x]        | [~]         | Many error sites wired; needs audit for completeness. |

## Appendix A: Expression forms

| Item                                      | Spec section | Lowering | Constraints | Goals | Unify | Defaulting | Generalize | Errors/Info | Notes |
|-------------------------------------------|--------------|----------|------------|-------|-------|------------|------------|-------------|-------|
| Literals (int/float/bool/nil/string/etc.) | A.1          | [~]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | Non-numeric literals still `todo!()` in lowering. |
| Operators (binary/unary)                  | A.2          | [x]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | Operator traits via `GlobalEnv` tables. |
| Records and field access                  | A.3, 4.5     | [~]      | [x]        | [x]   | [x]   | N/A        | [x]        | [~]         | No pattern records yet. |
| Control flow (`if`, `while`, `loop`, `for`, `break`, `continue`, `return`, pattern-if/while) | A.6 | [~] | [~] | [x] | [x] | N/A | [x] | [~] | Some lowering/constraint cases still `todo!()`. |
| Bindings and assignment (`x = e`, `*p = e`, `e.x = rhs`, `container[i] = rhs`, destructuring) | A.8 | [~] | [~] | [x] | [x] | N/A | [x] | [~] | Simple `x = e` generalized with value restriction; other LHS forms missing. |
| Casts (`e as Tcast`)                      | A.9          | [ ]      | [ ]        | [ ]   | [ ]   | N/A        | N/A        | [ ]         | Cast lowering and typing not implemented yet. |
