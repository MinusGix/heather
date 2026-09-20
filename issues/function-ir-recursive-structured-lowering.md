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

## Current implementation boundary

Ordinary `compile-x86` now consumes the recursive selection plan for reflected
tail-position unsigned matches. Both nesting directions in
`examples/x86-native/branches.hthr` retain live inputs and use the same
source/FunctionIR/physical-code path.

`function_ir_x86_lower::generate_structured` folds selected Dataflow, Sequence,
and Conditional plans into checked declarations. Leaf refinement reuses the
existing DAG emitter with computed local RegionHolds witnesses. Sequence
proofs carry placements by port ID using output/frame facts. Conditional
proofs use selector agreement, actual short-control execution, child spans,
and the common physical join. `StructuredCode` fixes both canonical bytes
and selected execution; `StructuredArtifact` requires layout, decoding,
result, memory, register-frame, and final-RIP evidence.

The public source artifact accepts an arbitrary entry machine, constructs its
input valuation, and closes internal graph obligations. Source-expansion
checking names the resolved definition. The CLI kernel-checks that artifact
and exact emitted-byte equality before publishing either file. RET, ABI,
instruction fetch/loading, and host assembly/linking remain external to this
assembly-export claim. Structured bodies are not yet accepted by `build-x86`.

The next bounded iteration's source-to-native path is implemented; validation
is recorded below. The broader issue remains open for multiple prefix outputs
and result joins (with [[function-ir-x86-join-placement]] owning reconciliation).
The source interface for future buffers/loops belongs to
[[function-ir-bounded-readonly-loop]]. Existing flat certificate APIs remain
available to their current callers.
The current slice explicitly refuses unsupported pressure, leaf operations,
and rel8 ranges and requires one result per prefix/join. No parser-specific
model, profile flag, kernel extension, or raised resource limit was added.

## Log

- 2026-09-20: Architecture review at 4db435c recommends this as the first implementation checkpoint: nested pure source conditionals through recursive structured lowering before adding buffer loops. docs/native-compiler-architecture-review.md records the findings; [[native-shared-lowering-milestone]] owns the end-to-end two-client acceptance criterion. No backend changes were made in the review.
- 2026-09-20: First implementation slice: added elaborated-source reflection of nested
  unsigned Boolean matches into the existing StructuredRegion, with payload
  binder depth handled by the shared arithmetic reflector. Added recursive
  Dataflow/Sequence/Conditional selection using stable value-ID placements,
  existing leaf selection, explicit carried results, clobber unions, and checked
  rel8 range proposals. Source expansion is emitted from FunctionIR through
  structured declarations and names the resolved source definition.

  This is a staging boundary, not completion of the next bounded iteration:
  the source-expansion equality is not a StructuredRegionHolds witness or a
  machine-execution theorem. Recursive physical proof composition and the final
  published-byte/source artifact remain to implement. The native CLI still
  rejects nested source functions; no unchecked plan is exported. Current
  selection restrictions include one result per prefix/join, arithmetic or
  constant source leaves, unsigned comparison guards, and explicit pressure/range
  refusals. Tests cover both nesting directions, live inputs, reordered port
  interfaces, malformed placements, pressure/range refusals, source agreement,
  and stale-source/wrong-operand controls. Validation is in progress.
- 2026-09-20: Validation: all five focused recursive-source tests pass. Plain `scripts/test`
  passes 2837 tests, 0 failed, 5 ignored, including the existing native export
  and stack-save certificate gates. Issue consistency and `git diff --check`
  pass. The physical-certificate/publication checkpoint above remains open.
- 2026-09-20: Implemented the recursive physical certificate fold and ordinary compile-x86
  integration. The shared StructuredCode model fixes bytes and selected execution;
  its artifact requires layout/decoding, source result, memory/register frames,
  and the common exit RIP. Computed local graph valuations reuse existing DAG
  refinement, and the source artifact closes graph assumptions for an arbitrary
  entry machine. The CLI verifies exact published bytes before output. Both
  nesting directions use the same path with no new profile or application model.

  Focused kernel tests pass, including local rejection of wrong targets, encoded
  bytes, carried bindings, clobbers, output destinations, and stale source. The
  canonical TEST representative is proved equal to execute_normal. Native and
  full-suite validation are in progress. Multi-result interfaces remain beyond
  this bounded checkpoint; the issue is not yet closed.
- 2026-09-20: Focused validation completed: all three recursive physical-certificate tests
  pass, including six dishonest artifact controls. Both ordinary compile-x86
  exports assemble and execute correctly on 10,036 input pairs each. The
  canonical TEST equivalence lemma also passes an independent capped check.
  The final plain scripts/test run is underway.
- 2026-09-20: Final validation: plain `scripts/test` passed 2841 tests, 0 failed, 5 ignored.
  This includes both native branch exports, all recursive certificate controls,
  and existing arithmetic/call/stack-save gates. Each new native function passed
  10,036 input pairs. `git diff --check` and issue consistency checks pass.
  The bounded nested-source-to-native checkpoint is complete. The broader
  multi-prefix-output/multi-result acceptance remains open; no issue scope or
  proof boundary was silently declared complete.
- 2026-09-20: The shared typed source-interface prerequisite is being extended under
  [[native-bounded-loop-certificates]]; the ordinary recursive reflector now also
  serves byte/Boolean predicates. Multi-result physical joins remain open here.
