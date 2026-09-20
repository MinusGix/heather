---
title: Generalize x86 lowering over recursive StructuredRegion trees
status: open
labels: [compiler,function-ir,x86,control-flow]
blocked-by: [function-ir-conditional-regions]
created: 2026-09-01
updated: 2026-09-20
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

## Next bounded iteration

Start with two ordinary source functions that nest unsigned conditionals in
opposite arms and retain a live input across a branch. Extend elaborated
source reflection alongside recursive selection: manually constructed IR
fixtures alone do not satisfy this checkpoint. Name the actual resolved
source function in the certificate.

Use existing arithmetic and physical branch lemmas, explicit port placements,
and structured proof emission. A fixed common result placement and honest
pressure/range refusals are acceptable first. Demonstrate complete selected
execution and published bytes without example-specific register/RIP theorem
families. Reject wrong carried bindings, clobbers, destinations, and stale
source locally under normal limits.

This is the first step of [[native-shared-lowering-milestone]], before memory
or loops. The broader multi-result acceptance above remains in scope for
subsequent iterations; the first slice does not need a general allocator.

## Log

- 2026-09-20: Architecture review at 4db435c recommends this as the first implementation checkpoint: nested pure source conditionals through recursive structured lowering before adding buffer loops. docs/native-compiler-architecture-review.md records the findings; [[native-shared-lowering-milestone]] owns the end-to-end two-client acceptance criterion. No backend changes were made in the review.
