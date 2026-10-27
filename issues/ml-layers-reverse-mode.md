---
title: Layer grammar with reverse mode defined once and proved once
status: open
labels: [design,machine-learning]
area: machine-learning
milestone: [ml-layers]
created: 2026-10-21
updated: 2026-10-27
---

A small layer grammar (linear, pointwise activation, compose, fork,
residual) over [[ml-tensor-shapes]], with a forward semantics and a reverse
mode defined once as a transformation over the grammar
(`docs/wick-survey.md` §3.5). Per-layer work is only the primitive rules.

Correctness is the pairing identity `⟪backward dy, δ⟫ = ⟪dy, df δ⟫` with
`df` pinned to a real derivative, which Wick never managed generally (its
Phase 2): for polynomial layers the formal derivative, for transcendental
activations the derivative of [[real-functions-and-derivatives]]. Keep
Wick's separation between a practical backward pass (defined for every
layer, subgradients allowed) and the theoretical claim of differentiability.

First customer: a two-layer network that evaluates at `Rat`, with its
gradient checked against the formal derivative by evaluation at concrete
values. Longer term this is a compiler pass and belongs with `hih-passes`.

## What it assumes from elsewhere

- **[[ml-tensor-shapes]]** owns shapes and pairings. Assumed here: only a
  computed pairing per shape.
- **[[finite-linear-algebra]]** owns matrices. Assumed here: matrix-vector
  products and transpose with their basic laws.

## Log

- 2026-10-27: The formal derivative and dual-number evaluation of polynomial programs are in [[formal-power-series]] (docs/analysis-foundations-design.md §5); reverse mode as an instance of a reverse differential structure is [[differential-structures]] (§3.1).
