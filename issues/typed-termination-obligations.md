---
title: Build termination obligations from typed local contexts
status: closed
labels: [frontend,elaboration,termination,proofs,ergonomics]
created: 2026-09-14
updated: 2026-09-14
---

## Problem

The checked calculator in `docs/showcase/calc_parser.hthr` repeats
`Parsed(list_len(ts))` on local bindings and introduces an annotated
`remaining` variable before matching `left.rest`. The measure pass's
`Rewrite::scrut_ty` only recognizes variables whose surface type it already
knows; inferred lets and field expressions lose information the ordinary
elaborator can determine. `lift_obligation` selects binders by direct name
occurrence in the goal/discharge rather than closing over their dependent
types. These restrictions expose the lowering machinery in source programs.

## Direction

Generate decrease obligations in typed local contexts, with the group's
signatures available provisionally and recursive calls represented through
the well-founded recursion interface. Lift each goal together with the
transitive dependencies of its local variables' types and relevant match
equations. Preserve source locations. This is a design direction, not a
requirement to duplicate elaboration or choose a particular intermediate IR.

Provisional recursive references must never become unchecked global
assumptions. A call's result cannot justify its own precondition; a prior
valid call's postcondition may justify a later call. All emitted definitions
and proofs still pass the kernel gate.

## Acceptance

- The calculator can infer the local successful parse results and match
  `left.rest` directly without annotations added solely for lifting.
- Single and mutual decreases functions retain their current semantics,
  declaration-order rank behavior, and explicit proof discharges.
- Lift dependent contexts completely: an open element type, a value-indexed
  record, and a match equation needed by another hypothesis's type.
- Refuse nondecreasing recursion, circular use of a call's own result,
  ill-typed arguments, and false decrease evidence. No unproved goals leak
  from a failed group into subsequent declarations.
- Exercise literal and neutral inputs in checking positions and retain
  useful source diagnostics for a failed obligation.

## What it assumes from elsewhere

- **[[mutual-recursion-declarations]]** owns group formation and rank rules;
  assumed here: those rules remain the recursion contract.
- **[[termination-measures]]** owns the measure surface; assumed here:
  existing well-founded lowering remains the proof boundary.
- **[[showcase-token-parser]]** owns the concrete client; assumed here:
  it supplies a checked baseline for removing lifting-only annotations.
- **[[termination-local-evidence]]** owns automatic selection of local
  decrease evidence; this issue supplies the typed context it consumes.
- **[[parser-combinator-library]]** owns the downstream library customer.

## Log

- 2026-09-14: Implemented isolated ordinary-elaborator type queries for local
  initializers and computed scrutinees, with provisional signatures confined
  to the query's local telescope. Recovered annotations are rechecked against
  inferred types. Lifted contexts now close over dependent types and typed
  match equations; computed scrutinees get a fresh internal binding. The
  calculator infers its successful parse-result locals and matches their
  fields directly. Failed recursive families use session rollback. Design
  and acceptance coverage: `docs/typed-termination-contexts-design.md`.
- 2026-09-14: Full `scripts/test`: **2655 passed, 0 failed, 5 ignored**.
  The checked calculator retains all grammar/result equations and refusal
  controls after removing five `Parsed(...)` annotations and three
  `remaining` aliases. Automatic use of local proofs remains owned by
  [[termination-local-evidence]]; this type-recovery/lifting scope is complete.
- 2026-09-14: The isolated benchmark gate reports four Nat timing flags and
  no slope failures, recorded under [[kernel-benchmark-nat-baseline-drift]].
  The kernel and baseline are unchanged. Tracker and whitespace checks pass.
