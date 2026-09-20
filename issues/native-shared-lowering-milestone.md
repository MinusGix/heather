---
title: Demonstrate shared native lowering with independent bounded buffer loops
status: open
labels: [compiler,x86,architecture]
created: 2026-09-20
updated: 2026-09-20
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
