---
title: Compile a checked byte-buffer cursor recognizer
status: closed
labels: [compiler,x86,parsing,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Scope

First native step toward the showcase text calculator: compile a source-defined
single-byte recognizer with a guarded byte load from caller-owned storage. Input
bytes, length, and cursor arrive at runtime. Match advances one byte; mismatch
and exhausted input preserve the cursor. A fixed-buffer host adapter provides
input/output without implementing recognition or allocating parser storage.

## Acceptance

- Check the unsigned cursor bound before loading; model readable, canonical,
  nonwrapping byte access explicitly, with no read premise on the empty path.
- Tie actual emitted bytes and branch targets to the machine model and the
  source classifier; certify status, cursor, and memory/register preservation.
- Run one compiled executable against varying inputs, including all byte values,
  nonzero cursors, empty input, and an inaccessible byte beyond the input extent.
- Reject stale encoding, branch, source-result, and memory-access evidence.
- Keep verification within existing proof and process limits.

## What it assumes from elsewhere

- [[x86-64-machine-model]] owns ordinary instruction semantics.
- [[x86-native-export]] owns the existing assembly-export and host ABI boundary.
- [[x86-composed-summary-test-cpu-margin]] owns unit-test resource headroom;
  new native acceptance coverage belongs in a separate bounded target.
- [[parser-combinator-library]] owns the existing parser semantics. This first
  primitive does not yet compile its combinators or the whole calculator.

## Log

- 2026-09-19: Implemented the explicit buffer-cursor assembly profile and the fixed-storage host driver. One compiled recognizer passes runtime strings, all 65,536 byte/cursor pairs, unchanged-memory checks, and guard-page controls. Generic certificates now cover status/cursor refinement, conditional read permissions, preserved registers/memory, path execution, and reaching the return instruction at an arbitrary code base. Factored address-advance proofs and finite branch-span checks to retain default fuel. [[x86-buffer-decimal-parser]] owns the next parser slice.
- 2026-09-19: Targeted native acceptance is green, including standalone certificate replay and five refusal controls (encoding, branch target, cursor, read permission, stale source). The driver accepts a full 256-byte buffer and refuses longer input. Added publication refusals for replaced bundled models and oversized classifier branch spans. Disassembly independently confirms CMP/JAE before MOVZX and all paths joining at RET. Full plain `scripts/test` is running; budgets and kernel rules are unchanged.
- 2026-09-19: The first full run passed all functional targets, including bundled-model and oversized-body publication refusals, but the Heather formatting gate rejected whitespace in the new machine model (2832 passed, 1 formatting failure, 5 ignored). Applied the repository's Heather formatter to that one file and started a new plain full run. The new native target used 33.0 CPU-seconds under the unchanged 300-second per-process rail.
- 2026-09-19: Final plain `scripts/test`: 2833 passed, 0 failed, 5 ignored (294 seconds wall). Closed the first runtime-input recognizer milestone: compiled source classification, guarded byte access, checked cursor/status and memory/register behavior, execution paths and relocated return joins, native exhaustive/guard-page cases, proof mutations, model-replacement refusal, and bounded-layout refusal all pass. The fixed-storage demo is documented in docs/x86-64-buffer-cursor.md. RET/host ABI and I/O remain the explicit assembly-export boundary. [[x86-buffer-decimal-parser]] owns decimal runs; [[x86-composed-summary-test-cpu-margin]] retains the existing CLI unit target's tight resource margin. No kernel or budget changes.
