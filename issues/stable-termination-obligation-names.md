---
title: Give manual termination proofs stable source-level handles
status: closed
labels: [frontend,syntax,termination,proofs,ergonomics,design]
created: 2026-09-14
updated: 2026-09-14
---

## Problem

`on ?dec2 := small` identifies a recursive call by traversal order. Inserting
an earlier call changes the association between generated numbers and sites.
The calculator provides a concrete example of source code depending on that
numbering. Named manual discharges should survive unrelated edits.

## Direction

Allow the author to attach a stable name to a recursive call's decrease
obligation, then discharge that name. Decide the syntax with small examples;
no particular spelling is approved yet. Use source identity internally as
needed, but do not make an automatically generated source-offset/hash name
the user-facing contract. Retain existing numbered discharges compatibly.

## Acceptance

- Inserting or reordering independent recursive calls does not retarget a
  user-named proof.
- Multiple calls to the same callee, nested calls, and mutual-group calls
  have distinct, correctly scoped handles.
- Diagnose duplicate, unknown, and dangling labels at their source sites.
- Wrong evidence for a named site is refused even if it proves a different
  site's obligation. Existing `?decN` programs continue to check.
- Avoid collisions with ordinary goal-hole names and names introduced by
  generated Result propagation; document the chosen scoping rule.

## What it assumes from elsewhere

- **[[termination-measures]]** owns the decrease obligation itself; assumed
  here: each recursive call has an identifiable obligation site.
- **[[termination-local-evidence]]** owns automatic use of available proofs;
  stable naming serves the remaining manual cases.
- **[[parser-combinator-library]]** is the downstream library customer.

## Log

- 2026-09-14: Implemented `call(args) decreasing label` with
  `on decreasing label := proof;`. Labels have a declaration-local namespace
  separate from ordinary holes; numbered discharges remain compatible for
  unlabeled calls. Call metadata survives Result lowering, and isolated type
  recovery strips it before inference. Duplicate, unknown and nonrecursive
  labels receive source diagnostics. The ordinary obligation lifter and
  kernel check each proof against its own call. Design:
  `docs/stable-termination-labels-design.md`. Focused elaborator acceptance:
  **39 passed, 0 failed**; editor grammar corpus: **9 passed**.
- 2026-09-14: Full `scripts/test`: **2666 passed, 0 failed, 5 ignored**.
  Tracker and whitespace checks pass. Scoped acceptance complete.
