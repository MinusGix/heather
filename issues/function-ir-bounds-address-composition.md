---
title: Check bounds-selected reads and word cursor/address proofs
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-20
updated: 2026-09-20
---

Connect a selected unsigned bounds test to the actual TEST/JZ decision, and
prove the word/Nat cursor and address obligations needed by read-only clients.

## Scope

- General access-aware composition over existing pure StructuredCode leaves,
  explicit byte-read steps, sequences, and actual machine branches.
- Selected-path execution evidence only; no grant is required by the end arm.
- Forward labels resolved from child lengths and kernel-checked against literal
  published bytes. Unsupported short spans decline.
- Generic nonwrapping addition and unsigned comparison bridges; loop-specific
  consumers relate base+cursor, ReadsByte, and cursor advancement to those facts.
- Compiled source guard, ADD address calculation, read, and body exercised
  together, with open-memory certificates and independent native clients.

## What it assumes from elsewhere

- [[function-ir-byte-load-composition]] owns the granted-byte load and typed read/body contract.
- [[function-ir-typed-source-publication]] owns source-named pure body artifacts.

## Boundaries

This is one selected bounds/read transition. Budget selection, carried-state
updates, backward edges and a complete bounded trace remain owned by
[[native-bounded-loop-certificates]]. Low-canonical data-address evidence stays
explicit. RET, instruction fetch, faults and the host ABI remain external.
The existing pure IR is unchanged; access composition reuses its certificates.

## Log

- 2026-09-20: Implementation and focused validation in progress.
- 2026-09-20: Added access composition with path-local ExecuteAccess, exact byte/layout publication, general memory preservation, width-generic nonwrapping addition/comparison/successor bridges, and loop word/address/read transport. Integrated source-selected guard/address/read clients and refusal controls are under focused validation. Budget/back-edge/complete-trace work remains with the parent issue.
- 2026-09-20: Focused integrated validation passed: both typed native clients, open-memory successful-read/end artifacts, reversed guard/wrong address/wrong byte/stale branch-byte refusals, and branch-range declines. Native execution covers 196,628 calls, including final-page-byte reads and denied pointers on skipped paths. The final plain scripts/test is running; no resource limits were changed.
- 2026-09-20: Final validation complete: plain scripts/test passed 2866 tests, 0 failed, 5 ignored. The general bounds/model target and integrated guarded-read target both fit the unchanged CPU/memory limits. Diff and issue consistency checks pass. This closes the single-transition bounds/address checkpoint; budget selection, carried updates, back edges, and bounded traces remain under native-bounded-loop-certificates.
