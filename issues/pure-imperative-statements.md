---
title: let mut, :=, for, while and early exit in pure functions, lowered to folds
status: open
labels: [frontend,syntax,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-10-31
---

Round R3 of `docs/compiler-milestones-proposal.md` (§3.1, §3.3, §7): local state and loops in pure functions.

## Scope

- `let mut`, `:=`, `for` over lists and ranges, `while … decreases` and `while … fuel`, and early exit, lowered to folds or structural recursion, with the mutable locals as a state tuple.
- Unfolding equations generated beside each lowered loop, and the loop body exposed as a step function (`f::step`).
- The same forms inside a carrier block from [[binding-statements]].
- Negative controls: `:=` to a local that is not `mut`, `break` outside a loop, and `while` with neither a measure nor fuel. Each is refused with its reason.
- State the elaboration cost of a large lowered body as a shape. If it grows superlinearly, generate named step functions by default.

## Done when

The decimal formatter and `wc`'s step are written imperatively, and their theorems are proved by the existing tactics with no hand unfolding.

## What it assumes from elsewhere

- **[[sequencing-surface-design]]** owns the lowering.
- **[[loop-invariant-rules]]** owns the invariant rule over these loops.
