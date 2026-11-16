---
title: Discharge decrease obligations from available local evidence
status: closed
labels: [frontend,elaboration,termination,proofs,ergonomics]
created: 2026-09-14
updated: 2026-09-14
---

## Problem

The calculator already binds `small`, a proof that the returned tail is
shorter than the original input, but must also write `on ?dec2 := small`.
The current lifter can omit a local fact unless the explicit discharge
mentions it. A termination goal should be able to consume evidence already
present in its local context.

## Scope

Try compatible local proof terms against the decrease goal before requiring
an explicit discharge. Feed relevant local arithmetic hypotheses to the
existing closer as appropriate. Handle instantiated dependent types through
ordinary conversion; do not define an unrestricted new proof-search engine.
Decide and document how proof fields on local records become available,
with bounded selection rather than eagerly traversing every record.

## Acceptance

- The calculator's two returned-tail calls use their existing `small`
  facts without `on ?dec2 := small`.
- A direct local proof, a dependent local proof, and an intentionally exposed
  remainder/progress proof field can discharge the corresponding obligation.
- Unrelated facts and unspellable unrelated context entries do not change the
  accepted program or mask the relevant failure.
- A false, reversed, or insufficient inequality is rejected. Evidence from
  the very call being justified is unavailable; evidence from an earlier
  validated call remains usable.
- Manual discharges and the default arithmetic closer continue to work;
  failures explain the actual remaining decrease goal.

## What it assumes from elsewhere

- **[[typed-termination-obligations]]** owns typed obligation contexts;
  assumed here: the solver can inspect admissible local evidence.
- **[[stable-termination-obligation-names]]** owns manual source handles;
  this issue reduces how often a manual handle is needed.
- **[[parser-combinator-library]]** owns consumption contracts; assumed here:
  local evidence may arrive through a library record's proof field.

## Log

- 2026-09-14: Implemented nearest compatible local proof selection and a
  checked, bounded Omega attempt with relevant inequalities. Manual proofs
  retain priority. Record fields participate through explicit bindings, with
  checked field-signature recovery for unannotated projections. The calculator
  removes both ordinal discharges. Design and limits:
  `docs/language/recursion/termination-local-evidence-design.md`. Focused acceptance: **41 passed**;
  full `scripts/test`: **2659 passed, 0 failed, 5 ignored**. Negative controls
  reject false, reversed, insufficient, circular, and invalid manual evidence;
  unrelated unknown locals do not prevent direct proof selection.
