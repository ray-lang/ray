1. Current Solver Architecture

Ray currently uses a single global constraint list containing:
	•	Equality constraints: t1 == t2
	•	Class predicates: Class(name, head_ty, params)
	•	HasField(base, name, ty)
	•	Recv(receiver_ty, expr_ty)

The high-level pipeline:
	1.	Solve equalities
	2.	Run improvement (now largely replaced by the Goal Solver)
	3.	Default unresolved meta variables
	4.	Run improvement again (post-default)
	5.	Report ambiguities and unsolved predicates

Old improvement handled:
	•	Multi-parameter type class reasoning
	•	Instance resolution
	•	Receiver-based inference
	•	Field-based inference
	•	Some default-driven inference
	•	Polymorphism timing issues

The Goal Solver is intended to replace this, but the surrounding architecture still assumes old behavior, so there are mismatches.

---

2. Architectural Constraints/Goals

◼ Unannotated Free Functions Are Allowed
	•	Only free functions (top-level standalone functions) may be fully unannotated.
	•	They act like “script mode”: global constraint solving over their body.
	•	They may still produce type schemes if their RHS is syntactic value.

◼ Trait/Impl Methods Must Be Fully Annotated
	•	No inference inside trait/impl items.
	•	This follows Rust’s item-isolation rules for coherence.

◼ Value-Restricted Generalization
	•	Only syntactic values generalize.
	•	Local non-value let bindings are monomorphic.
	•	No ML-style implicit polymorphism for arbitrary expressions.

◼ Type Classes Have No Fundeps, No Injectivity
	•	Class parameters are independent unless usage site forces equality.
	•	e.g. Lt['a,'a] within a function implies 'a == 'b only for that call, but Lt['a,'b] alone implies nothing.

◼ Defaulting Is Cosmetic and Must Run After Goal Solver
	•	Defaulting must not perform inference.
	•	It should only fill in leftover metas that the goal solver cannot determine.

These constraints shape everything else that follows.

---

3. Multi-Parameter Type Classes (Current Behavior)

Ray’s type classes are genuinely multi-parameter:
	•	Add['a,'b,'c]
	•	Lt['a,'b]
	•	Index['a,'b,'c]
	•	Deref['a,'b]

Ray does not support:
	•	Functional dependencies
	•	Type families
	•	Injectivity
	•	Subtyping
	•	Real union types

Therefore:
	•	The solver cannot infer relationships purely from class definitions.
	•	Only usage-site constraints like Lt['t,'t] allow equalities to arise.
	•	The system currently struggles to propagate these equalities deeply enough.

This is one of the biggest sources of brittleness.

---

4. Instance Representation (Current State)

Instances now store a canonical instance scheme:
	•	vars: quantified type vars
	•	head: predicate expressed in terms of these vars
	•	predicates: instance context

This resolved the old problem where ?sNN leaked everywhere.

Remaining difficulties:
	•	Instantiation still requires generating fresh meta vars
	•	Rigid metas may block valid instance selection
	•	Unification must avoid creating loops
	•	by_instance_scheme needs better integration with the goal solver

This area is improved, but brittle.

---

5. Goal Solver (New Component)

Intended responsibilities:
	•	Consume predicates coming from term-solver
	•	Resolve class predicates using instances
	•	Trigger field/receiver inference
	•	Derive equalities from schemas (e.g. Lt['t,'t])
	•	Leave residual predicates for later reporting

Current limitations:
	•	Does not fully replace old improvement
	•	Does not propagate enough equalities
	•	Defaulting still happens too early
	•	Multi-parameter behavior not solved deeply enough
	•	Not integrated with generalization timing

The biggest missing piece is schema-driven param linking for multi-parameter predicates.

---

6. Generalization Model (Stable)

Ray uses value-restricted generalization:
	•	Only syntactic values generalize
	•	Top-level items can introduce type schemes
	•	Local non-values remain monomorphic
	•	This is not the current problem area

Generalization rules are stable and not the source of recent issues.

---

7. The Big Picture Problem (Reconciled)

We are in a hybrid system:
	•	Old improvement was removed
	•	A new goal solver is only partially in its place
	•	Instance schemes were upgraded, but not fully integrated
	•	Constraint solving is still global rather than structure-aware
	•	Multi-parameter type classes have no schema-level param linking mechanism
	•	Defaulting steps rely on missing equalities
	•	Lack of constraint tree/binding-group structure makes phases interact poorly

This explains brittleness around:
	•	Multi-parameter classes
	•	Defaulting
	•	Polymorphism
	•	Instance selection
	•	Optional/nilable handling

Nothing is fundamentally broken — but nothing is fully coherent yet.
