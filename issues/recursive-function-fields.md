---
title: Surface inductives with recursive function-typed fields, lowered through W
status: open
labels: [inductives,elaboration,effects,design]
area: interaction-trees
milestone: [it-function-fields]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `it-function-fields` submilestone (`docs/roadmap.md`):
let a surface inductive declare a recursive function-typed field, such as an
interaction tree's continuation `Vis(c: E.Cmd, k: E.Resp(c) -> Tree)`, and
match and recurse over it. Today `reject_function_fields`
(`crates/elab/src/inductive.rs`) refuses it.

This is interaction-tree work, with ITrees as the driving client. The same
lowering also opens surface `Acc` and other infinitely branching types.

## What it assumes from elsewhere

- **[[inductive-compiler]]** owns the tier scheme and says such a field is
  tier 2, W-lowered. Assumed here: only that tier 2 lowers through the
  kernel's `W` former. Acc via W is already kernel-checked
  (`docs/acc-via-w.md`).
- **[[interaction-trees-container-model]]** owns the tree library this
  serves. Assumed here: only that its continuation is a function of the
  response type, with events written as containers.

## Done when

`Vis(c, k)` declares at the surface, with structural recursion through `k`
and a match on the tree, and the generated terms are tested on all four axes
of `docs/testing-generated-terms.md`.
