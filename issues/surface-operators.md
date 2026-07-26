---
title: "Operators, methods, and calc for the surface"
status: closed
labels: [frontend,syntax]
created: 2026-07-23
updated: 2026-07-26
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
