---
title: "Unified match: termination checking, IH = self-call"
status: closed
labels: [frontend,elaboration,syntax]
created: 2026-07-23
updated: 2026-07-24
---

The strong unification decided in docs/sketches/surface-v1.md §1
([[surface-syntax]]): `match` is the only eliminator form; a structurally
guarded recursive self-call *is* the induction hypothesis, so a theorem
proved by induction is just a recursive function — proof mode and function
mode are literally one language. The elaborator compiles guarded self-calls
into the kernel recursors (`elim_Nat` now; `case`/`elim_W` as the surface
grows); the stage-1 explicit-ih arm (`Succ(k, ih)`) stays as the low-level
fallback.

Work items:

- **Termination/guardedness analysis**: structural descent on one
  designated argument (the scrutinee chain). Start strict — self-calls
  only on the immediate predecessor variable(s) bound by the enclosing
  match — and widen only with evidence. Untrusted: a wrong analysis
  produces a term the kernel rejects (the lowering must *construct* the
  recursor, so there is no soundness hole, only rejection).
- **Lowering**: rewrite self-call occurrences in each arm into the arm's
  ih binder; multiple recursive fields (later, sums/W) get one ih per
  field in field order (surface-v1 rule). The dependent motive comes from
  the declared result type with the decreasing argument abstracted —
  recursive *theorems* need this (their statement mentions it), so this
  interacts with [[elab-stage2-metas]]'s motive synthesis; explicit `as`
  remains the escape hatch.
- **Surface**: self-calls need no new syntax; `induction`/`rec` keywords
  do not exist (never introduce them).

Acceptance: the Nat suite rewritten in recursive-theorem style (the
self-call form works without [[surface-operators]]; reads best with it) —
both spellings green.

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
- 2026-07-24: Landed for Nat. `Succ(k)` arm parses alongside the explicit-ih `Succ(k, ih)` fallback; the declaration's own name is in scope for its body (`Cx.selfref`), and inside a `Succ(k)` arm a guarded self-call lowers to the arm's hidden ih binder (`Cx.guard`, elab/src/lib.rs `elab_self_call`). Guardedness is strict as planned: saturated call, predecessor in the decreasing position, every other parameter passed *unchanged* — compared by binder, not by name, so shadowing cannot fake a descent. Acceptance met: crates/elab/tests/match_recursion.rs has the Nat suite in recursive-theorem style plus both spellings in one file, all kernel-checked.

Deferred (the one real limitation, diagnosed rather than left to the kernel): a self-call whose *non-decreasing* argument varies needs the motive to generalize it (M(z) = Pi(varying params). T), which means lambda-wrapping the arm bodies and applying `ih(e)` — and forces the match to the body root. This MVP is exactly the empty-generalized-set case of that algorithm, so widening is additive, not rework. Wanted eventually for accumulators and IH-generalizing proofs; nothing in the Nat suite needs it.
