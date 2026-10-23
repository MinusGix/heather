---
title: "Operators, methods, and calc for the surface"
status: closed
labels: [frontend,syntax]
created: 2026-07-23
updated: 2026-08-13
---

The ergonomics layer the sketches use freely and stage 1 lacks
([[surface-syntax]] rounds 1–3): infix operators, method-call syntax, and
`calc`. Stage-appropriate slice — full traits are NOT needed for any of
this ([[compile-typeclass-design]] owns resolution policy); a fixed
name-directed resolution does for now.

- **Operators**: `+` → `add`, `*` → `mul`, `<` → `lt` (fixed table first;
  the decorated-operator grammar `+_Z` / `⟦R⟧_s` and its trait hookup come
  with the real trait design). `==` already exists as the Id former.
  Precedence: the boring standard one, written down once in the parser.
- **Method calls**: `x.f(args)` resolves `f` in the namespace of `x`'s
  head type former (`p.sym()`, `xs.len()`, `add_zero(n).cong(Succ)`).
  With [[elab-stage2-metas]], the receiver feeds inference so endpoint
  arguments vanish.
- **`calc` blocks** (surface-v1 §1): chained `== rhs := proof` steps
  desugaring to nested `trans` with the step endpoints as the intermediate
  terms — a documented mechanical lowering, no new kernel anything. Wants
  operators for readability and stage-2 inference for the endpoints, but
  neither is a hard blocker.
- Parsing note recorded in the sketches: parenthesized type application
  keeps `<` unambiguous as comparison.

Acceptance: add_comm's Succ arm written as a `calc` block reading like
surface-v1 §1; the Nat suite in method style green alongside the
call-style spelling.

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
- 2026-07-24: Landed as pure parser desugaring to ExprKind::Call — no AST, kernel, or elaborator change. (1) Infix operators via a fixed name table (+ -> add, * -> mul, < -> lt; only + exercised, mul/lt targets are future defs), precedence-climbing expr_bp with standard precedence (< < + < *), left-assoc; == stays the Id-former (parsed by ty()/calc, never an expr operator, keeping < unambiguous). (2) Method calls x.f(args) -> f(args, x) (receiver LAST, so stage-2 implicit endpoints infer from it: p.sym() -> sym(p)). (3) calc { e0 == e1 := p1, == ei := pi, ... } -> right-nested @trans over the step PROOFS with the step terms as EXPLICIT endpoints — the explicit endpoints give refl-steps their checking type (the reason calc can't be a blind trans-of-proofs fold). Single-step calc is the bare proof. New tokens: . + * < := (crates/syntax/src/lexer.rs). Acceptance MET: crates/elab/tests/operators.rs — add_comm's Succ arm as the surface-v1 §1 calc block, whole Nat suite in operator/method/calc style green (7 Psi-globals), method-style == call-style, incoherent calc kernel-rejected; 12 parser desugaring unit tests. Scope note: the sketch's .cong(Succ) needs higher-order cong + first-class function values (function types aren't in the surface yet) — deferred to the trait/function-value layer; the acceptance uses .cong_succ() and reads like §1 otherwise. split/on statement forms (surface-v1 §2) belong to [[goal-holes]]; unified self-call match (Succ(k) without ih) is [[match-recursion]].
- 2026-07-26: The deferred higher-order '.cong(Succ)' now has a scheduled home: [[surface-function-types]] (roadmap item 8), which is the function-VALUE half of what this issue's note attributed to the trait layer. cong over an arbitrary function needs only Pi + lambda, not traits, so it does not wait for [[compile-typeclass-design]].
- 2026-07-26: Sharpening the previous note: [[surface-function-types]] landed the function-value layer, so 'cong(f: Nat -> Nat, …)' is now writable and usable — but the literal deferred spelling '.cong(Succ)' still is NOT, because constructors are saturated-only and 'Succ' is not even a resolvable name. That remainder is [[constructors-as-function-values]]. This issue's deferral is half-discharged, not discharged.
- 2026-07-26: The deferral is now fully discharged: [[constructors-as-function-values]] landed, and 'p.cong(Succ)' elaborates as written (crates/elab/tests/constructor_values.rs::cong_at_succ_by_name). Note which half did it — 'Succ' became an ordinary resolvable name (a lambda at Pi(Nat).Nat), which is what reaches the INFERENCE position that cong's implicit endpoints put its first argument in; the eta-expansion half only covers checking positions. So '.cong(Wrap)' for a declared constructor is still not writable.
- 2026-07-27: Correction to this issue's item (2): the method desugaring no longer puts the receiver LAST, and the stated reason for that was never load-bearing -- implicit insertion is name-directed and indifferent to explicit-argument order, so the two unary examples given (p.sym()) could not distinguish the orders. As of 2026-07-27 the receiver fills the callee's `self` parameter, defaulting to the first explicit one, so p.trans(q) means trans(p, q). See [[method-receiver-position]].
- 2026-08-09: The 'fixed name-directed resolution does for now' stopgap is retired: symbols now resolve by a three-rung ladder (constraint binder -> designation at the operand's carrier -> the old fixed name as the last rung), docs/operators-onto-classes-design.md §4. The old table IS rung 3, so every pre-round file runs the same code — pinned by growth-invariant tests in operators.rs.
- 2026-08-11: Residue from bare-symbol-checking-carrier (2026-08-11): the deferral cliff. A symbol designated somewhere whose argument slot never unblocks (mconcat(++, Nil)-shaped — no later argument pins the carrier) now refuses with a message naming both workable spellings, where + previously inferred add and *taught* the carrier from the fallback's type. The refusal is the better answer (the taught carrier could be wrong, which is the argument is_checking_only makes everywhere else), but it is a behaviour change, confined to files that declare a designation for that symbol.
- 2026-08-13: `designation * at Nat := mul` is in lib/std/algebra/algebra.hthr as of 2026-08-13, so `*` at Nat is a table row rather than only the fallback rung. One consequence found and re-pinned: operators_onto_classes.rs's `a_symbol_with_no_rung_names_the_symbol` needed a probe that does NOT import `nat`, because the fallback name `mul` is no longer nowhere. Owner: [[std-nat-multiplication]].
