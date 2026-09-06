---
title: Name the shapes and suffix sums of non-recursive and parameterized declarations
status: open
labels: [elaboration,inductives,performance,representation,x86]
created: 2026-09-06
updated: 2026-09-06
---

Found by the 2026-09-06 x86 kernel round ([[function-ir-x86-proof-scaling]]).
After the kernel stopped re-comparing stored Π/Σ annotations, the five-node
FunctionIR/x86 module's kernel time was ~7.7 s, of which ~4.6 s was two
families of expected-vs-inferred type conversions that miss the syntactic
shortcut and then walk 50K–300K-character types in the value domain:

- `El (D#tycode^δ)` against the same declaration's **inlined** sum-of-Σs
  (constructor labels checked at a `Wf`/sum type; ~2.0 s / 1,988 queries), and
- a **suffix sum** spelled inline against the same suffix spelled with a
  named component (`inr` chains of a 16-constructor `Gpr`, 11-constructor
  `Instruction`; ~2.6 s / 813 queries).

The exact diffs showed one type spelled three ways in one module: fully
inlined (`Σ(…)((Σ…`), through a named code (`El (u475^δ)`), and as a boxed
code literal (`El «(«Σ…»`). The shape-code machinery of
[[wf-shape-annotation-slots]] (`GenDef::ShapeCode`/`ArityFn`,
`register_wf_slots`) is registered only for **recursive** declarations, and
`register_ty_code` only for **unparameterized** ones. Every x86 model type is
non-recursive (`Gpr`, `Instruction`, `Flags`, `Gprs`) or parameterized
(`MachineState<M>`), so none of them gets a name below the whole type, and
`inl`/`inr` annotations spell the suffix sums out at every level — O(n²) in
the constructor count per literal, paid in the value domain.

## Levers

1. Register suffix-sum codes (`D#tail_k`) and per-constructor payload codes
   for non-recursive unparameterized declarations, and spell the `inl`/`inr`
   annotations of constructor values and `case` spines with them. Each
   level then costs one δ and an `==`.
2. Monomorphized codes for parameterized declarations, keyed by the
   instantiation ([[unnameable-annotation-occurrences]] names the same
   copies): `MachineState<M>` is the one every x86 theorem states.
3. One spelling, not three: whichever of inline / named / boxed-code the
   elaborator writes for a shape, it should write everywhere the kernel
   will compare it against itself.

## Acceptance

- The five-node module's `El` vs sum and sum vs sum shortcut misses are
  gone or O(1) each; measure with the per-bucket miss timing the round
  used (temporary instrumentation at `Tc::conv_ty`, not landed).
- No change to the inline lowering the recognizers fingerprint
  (`lower_instance` stays the identity, per the shape-code round).

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns the shape-code machinery. Assumed
  here: only its registration boundary, which this issue widens.
- **[[function-ir-x86-proof-scaling]]** owns the workload.

## Log

- 2026-09-06: The invariant this boundary is a slice of: [[elaborator-canonical-type-spelling]].
