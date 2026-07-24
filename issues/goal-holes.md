---
title: "Holes and on-discharge (goal-oriented blocks)"
status: open
labels: [frontend,elaboration,syntax]
blocked-by: [elab-stage2-metas]
created: 2026-07-23
updated: 2026-07-24
---

The goal design of docs/sketches/surface-v1 §2 / v2 §2 / v3 §2
([[surface-syntax]]): named holes `?name` as first-class deferred
obligations, discharged in-block by `on` — with goals literally being the
elaborator's metavariables ([[elab-stage2-metas]] is a hard dependency: a
hole IS a `u : Trm(Γ ⊢ T @ l)` that survives to the end of the block
instead of being solved by unification).

Decided surface (sketches):

- `?name` / anonymous `?` holes; `on ?name := expr;` discharge, any order.
- Default names from the callee's proof-parameter name, ordinal dedup,
  provenance in the listing ("proof-parameter names are API").
- Discharge-by-statement `on _: P := expr;` — discharges *all* goals whose
  statement matches P.
- Auto-holes: an implicit proof parameter marked auto-defer becomes an
  anonymous goal at the call site (`xs[i]` sugar, later).
- NO positional filling; goal merging is hole-programming (v3 §2), not a
  feature.
- Unfilled goals at block end = error listing each goal with provenance —
  this listing is the "checker shows goal state" UX and the tooling face
  of the whole design; worth making good early.

Out of scope here, tracked in the sketches: solver meta-functions
(`on _: _ := solver(goal, …)`, v3 §2) — needs the modal layer surfaced.

## Log

- 2026-07-23: Opened as part of the granular issue split after stage 1.
- 2026-07-24: Related: [[surface-proof-automation]] (auto-refl + apply) builds on this engine — auto-refl is the simplest hardwired instance of the future solver slot; apply's multi-premise form is defer-into-a-specific-application, discharged by on.
