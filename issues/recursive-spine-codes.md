---
title: Name a recursive declaration's shape spine components
status: open
labels: [elaboration,inductives,performance,representation]
created: 2026-09-06
updated: 2026-09-06
---

[[inductive-spelling-codes-nonrecursive]] named the payloads and suffix
sums of **flat** declarations and left recursive ones alone, by charter and
by measurement (no recursive many-constructor type is on the x86 module's
path). A recursive declaration's `D#shape` code is still the inline
sum-of-Σs literal (`⌜S⌝`), so a constructor label's `inl`/`inr` chain
spells its suffix sums out at every level, and the kernel's decode of
`El (D#shape^δ)` meets the label's named-component spelling one level at
a time — the same O(n²)-per-literal cost the flat round removed, on `Ir`,
`Node`, `StructuredRegion` and every other wide recursive declaration.

The mechanism is the same: register `PayloadCode`/`SuffixCode` off the
*shape's* spine (`spine` already reads a `Wf`'s shape), spell `D#shape`'s
body over the names, keep `WfSlots::shape_decoded` as the guard copy of
the decode (it becomes `Sum(El (D#payload₀^δ), El (D#suffix₀^δ))`), and let
`respell_spine`'s positional path do the rest. The unknown is
`wf_slot_refs`' second guard copy and `unspell_shape_here`, which assume
the shape decodes to `El ⌜S⌝`.

## When

Triggered: the next round on a workload with a wide recursive declaration
where the sampler's `El^δ` vs `Sum` or `Sum` vs `Sum` rows are its labels
(the `ir_v1` / certgen fixtures are the obvious candidates). Measure
first with the sampler; one deliberate round.

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns `D#shape`/`D#arity` and their
  guards. Assumed here: only that `shape_decoded` is a second guard copy.
- **[[inductive-spelling-codes-nonrecursive]]** owns the spine-code
  mechanism. Assumed here: only its registration boundary.
