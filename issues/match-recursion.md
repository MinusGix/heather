---
title: "Unified match: termination checking, IH = self-call"
status: open
labels: [frontend,elaboration,syntax]
created: 2026-07-23
updated: 2026-07-23
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
