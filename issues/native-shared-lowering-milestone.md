---
title: Demonstrate shared native lowering with independent bounded buffer loops
status: closed
labels: [compiler,x86,architecture]
created: 2026-09-20
updated: 2026-09-24
---

## Scope

Own the integration acceptance criterion from
`docs/native-compiler-architecture-review.md`: two ordinary source programs
must share a native lowering/certificate path without adding per-application
machine models or register/RIP proof families. Calculator expansion is paused.
The specialized buffer profiles have been removed by user direction. This
milestone is an integration test for shared compiler features, with no
compatibility requirement for the removed scanner representation or ABI.

## Iteration order

1. [[function-ir-recursive-structured-lowering]]: compile nested pure source
   conditionals through shared recursive selection and physical certificates.
2. [[function-ir-bounded-readonly-loop]]: settle bounded source/IR iteration,
   carried state, selected reads, and exhaustion semantics.
3. [[native-bounded-loop-certificates]]: generate complete physical loop proofs
   from that shared selection path, with symbolic edges and checked frames.
4. This issue: compile occurrence counting, then first-match search, and verify
   the second client adds no new application-specific machine machinery.

Each step is independently reviewable. Do not add parser features or rebuild
both a native-only loop semantics and a separate FunctionIR loop semantics.

## Acceptance

- First demonstrate recursive source/FunctionIR/physical-branch composition
  with nested pure conditionals, including a live value crossing a branch.
- Settle the bounded source-loop and FunctionIR contract, including carried
  values, observable exhaustion, read-only memory dependencies, and the word/Nat
  counter relation before another native-only loop template is introduced.
- Compile occurrence counting and first-match search over caller-owned bytes
  with runtime input and needle through shared selection/certificate machinery.
- The second client adds source/specification/tests, with no application-specific
  machine model, instruction-pointer theorem family, or native profile template.
- Check complete source/execution/byte correspondence within an explicit export
  boundary, and reject incorrect guards, placements, targets, and source bodies.
- Retain existing resource limits and honest refusal of unsupported constructs.

## What it assumes from elsewhere

- [[function-ir-recursive-structured-lowering]] owns recursive branch selection
  and proof composition; this issue owns its integration into source clients.
- [[function-ir-x86-join-placement]] owns broader placement reconciliation.
- [[x86-symbolic-fragment-layout]] owns symbolic placement and displacement facts.
- [[byte-memory-access-model]] owns reusable access policy semantics; the first
  client only needs a read-only supplied-buffer subset.
- [[function-ir-bounded-readonly-loop]] owns the source/IR loop contract.
- [[native-bounded-loop-certificates]] owns complete native loop certificates.

## Historical context

[[x86-buffer-scan-loop-refinement]] and [[x86-buffer-decimal-parser]] record
withdrawn prototype work. Their closure records removal/supersession, not
completed scanner or decimal correctness proofs. The prototype is recoverable
from commit 4db435c and is not retained as active compiler infrastructure.

## Log

- 2026-09-20: [[native-bounded-loop-certificates]] now source-certifies the complete
  search body through general helper composition and two-constructor scalar
  results. Physical body/loop realization and Nat counting remain outstanding.
- 2026-09-20: By user direction, removed the two specialized buffer export profiles, their generators, five model modules, dedicated acceptance targets, examples/drivers, and build guides. Removed the profile-only parameterized valuation helper. General arithmetic, structured lowering, call summaries, shared-value/save-slot support, and test-isolation fixes remain. The implementation queue is now recursive source conditionals, [[function-ir-bounded-readonly-loop]], [[native-bounded-loop-certificates]], then this two-client integration check. The old scanner issues are retired as removed/superseded, without claiming their proofs were completed. Full-suite validation is in progress.
- 2026-09-20: Cleanup validation: plain scripts/test passed 2832 tests, 0 failed, 5 ignored. The count is three lower because the two retired buffer-profile targets contained three tests. Updated documentation links, issue tracking, and git diff --check pass. No references to the retired profiles remain in crates/, lib/, or examples/. The shared-path implementation issues remain open; this round removes the prototypes and establishes the iteration queue.
- 2026-09-20: Started [[function-ir-recursive-structured-lowering]] with source reflection,
  recursive selection, and source-expansion checking. Physical recursive
  certificates and native publication remain in that issue's next checkpoint.
- 2026-09-20: [[function-ir-recursive-structured-lowering]] now implements the bounded
  source-to-native checkpoint, including recursive physical certificates and
  ordinary assembly export. Full validation is pending in that issue; broader
  multi-result interfaces remain open.
- 2026-09-20: The bounded nested-source-to-native checkpoint in
  [[function-ir-recursive-structured-lowering]] passed full validation. The
  shared physical certificate/export path is now exercised by both branch
  shapes; multi-result interfaces remain in that issue.
- 2026-09-20: [[function-ir-bounded-readonly-loop]] now defines the shared source/IR
  semantic contract and two source clients; native body/loop realization is
  the next step in [[native-bounded-loop-certificates]].
- 2026-09-20: [[native-bounded-loop-certificates]] now has a shared typed frontend checkpoint:
  the two loop clients' byte predicate reflects through ordinary structured IR;
  whole-body and physical-loop realization remain outstanding.
- 2026-09-20: Physical composition and explicit multi-result placement now use shared recursive
  selection and certificate emission under [[function-ir-recursive-structured-lowering]].
  Composed prefixes carry multiple outputs plus inherited inputs by port ID;
  branches share per-port result destinations, and each result is proved over the
  same physical execution. Conditional helpers also reach ordinary scalar native
  export. Multi-result DAG slices can recompute shared work; the optimization is
  tracked in [[function-ir-shared-multi-result-dag]]. Byte/Boolean leaf operations,
  guarded reads, Nat representation, symbolic edges, and bounded traces remain.
  Validation is in progress.
- 2026-09-20: Physical composition/multiple-result placement checkpoint is complete and
  [[function-ir-recursive-structured-lowering]] is closed. Plain scripts/test:
  2854 passed, 0 failed, 5 ignored, including the new composed-helper native
  export on 10,036 input pairs and multi-result kernel certificate controls.
  The loop body's byte/Boolean dataflow selection, guarded loads, and complete
  bounded trace remain open; no native search_body certificate is claimed.
- 2026-09-20: The next shared-body checkpoint adds explicit zero-extended placements for
  widths 0–64, normalized constants/copies, narrow bitwise operations, and unsigned
  comparisons. Generic bitvector zero-extension laws support the proof generator;
  there is no byte_equal or search-specific machine rule. The complete search_body
  is the source-driven physical-certificate customer, including its Boolean carry
  and payload/discriminator outputs. Narrow add/subtract and signed comparisons
  remain explicit refusals, tracked in [[function-ir-narrow-arithmetic]]. Validation
  is in progress. Typed source publication, guarded loads, and bounded traces
  remain separate from this body-certificate checkpoint.
- 2026-09-20: Shared narrow-value/body-certificate checkpoint validated: plain scripts/test
  passed 2858 tests, 0 failed, 5 ignored. This includes kernel-checked search_body
  payload/discriminator certificates, source expansion, negative placement and
  signed-comparison controls, 2,560 independent execution cases, and existing
  native regressions. The checked-in generated x86 example matches the emitter.
  No resource limits changed. Typed source-to-machine publication, guarded reads,
  and complete bounded-loop traces remain open; this completes the body checkpoint.
- 2026-09-20: Typed source-to-machine publication is being completed under
  [[function-ir-typed-source-publication]], using shared per-result physical
  artifacts and explicit normalized argument placements. Guarded reads and
  bounded-loop execution remain subsequent work here.
- 2026-09-20: [[function-ir-typed-source-publication]] is complete: typed source-named physical
  artifacts now cover scalar and choice results, including search_body. Full suite:
  2860 passed, 0 failed, 5 ignored. Guarded byte reads and bounded-loop execution
  remain next; the native CLI calling convention is unchanged.
- 2026-09-20: The normal-path read boundary is being implemented under
  [[function-ir-byte-load-composition]]: a shared MOVZX byte-load contract and
  composition with typed source bodies. Selecting the actual bounds guard and
  bounded-loop trace remain subsequent work here.
- 2026-09-20: [[function-ir-byte-load-composition]] is complete: a checked successful byte-load
  prefix now feeds typed scalar/multiple-result bodies and publishes exact bytes.
  Plain full suite: 2863 passed, 0 failed, 5 ignored. Selecting the bounds branch,
  relating the address to the Nat cursor, and complete bounded traces remain here.
- 2026-09-20: The next shared access-composition checkpoint is [[function-ir-bounds-address-composition]], connecting a compiled bounds guard and address ADD to the typed read body.
- 2026-09-20: [[function-ir-bounds-address-composition]] is complete; shared access composition now connects compiled bounds/address code to typed read bodies. Plain full suite: 2866 passed, 0 failed, 5 ignored. Complete bounded-loop selection remains open.
- 2026-09-24: Steps 3 and 4 are met in substance (2026-09-24). Occurrence counting and first-match search compile through one generator (`generate_elaborated_loop_x86`) at one placement, with complete source/execution/byte certificates in an explicit export boundary, native runs against guard pages, and refusals at local boundaries. The second client added its source and one source-level fact about its step (`count_body_advances`), and no machine model, IP-theorem family or native template. See [[native-bounded-loop-certificates]] (closed) and `docs/native-bounded-loops-design.md`. Left open for the user to close.
