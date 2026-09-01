---
title: Generalize x86 lowering over recursive StructuredRegion trees
status: open
labels: [compiler,function-ir,x86,control-flow]
blocked-by: [function-ir-conditional-regions]
created: 2026-09-01
updated: 2026-09-01
---

The first structured backend handles the deliberately useful normal form
`Sequence(comparison, Conditional(Dataflow, Dataflow))`: one materialized bit,
inherited 64-bit arguments, and one common 64-bit result. FunctionIR semantics
and validity already permit arbitrary nesting.

Generalize selection and proof composition recursively without flattening the
structured graph or inventing bespoke generators for every shape.

## Acceptance

- Recursively lower `Dataflow`, `Sequence`, and `Conditional` through one
  structured selection interface.
- Carry multiple live prefix outputs and inherited inputs by stable port ID,
  with explicit placement environments rather than positional special cases.
- Support nested conditionals and sequences in either branch.
- Join multiple results with explicit per-port placements.
- Preserve the current local proof boundaries: leaf refinement, frame facts,
  selector agreement, and explicit intermediate states.
- Produce useful structured decline errors when a leaf operation, placement,
  register pressure, or machine-control shape is unsupported.
