---
title: Compose straight-line source callers through reusable leaf summaries
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Scope

Generalize the native executable caller beyond the fixed forwarding/XOR/two-call
shapes. Accept resolved straight-line `BitVec(64)` expressions and `let` bindings
around calls to one explicitly selected arithmetic leaf, including computed or
reordered arguments and values live across calls.

## Acceptance

- Check a source-expression theorem over arbitrary inputs against the caller.
- Reuse one callee summary at every call with independently checked argument,
  fetch, access, and successor premises.
- Carry live values through the existing preserved-register contract; reject
  pressure that requires unsupported spills.
- Connect the actual emitted executable to the source result for its arguments,
  including wrapping arithmetic, and restore RSP.
- Reject stale source plans and incorrect register facts. Keep existing native
  stack-local, two-placement, and mutation controls.
- Complete the plain full `scripts/test` lane.

## What it assumes from elsewhere

- [[x86-reusable-callee-certificates]] supplies reusable leaf summaries.
- [[x86-calls-stack-frames]] owns broader call graphs and callable frame profiles.
- [[x86-call-memory-footprints]] owns generic frame allocation and aliasing.

## Implementation

`docs/x86-64-call-composition.md` records the supported fragment and proof
boundary. The selector uses four preserved temporary registers plus two input
registers. It accepts at most four expanded calls and 64 expression nodes,
within the existing 128-instruction trace bound. This entry-only caller does
not export a generic caller ABI contract or introduce spilling. Original
specialized stack-local and two-placement profiles remain supported.

The executable example combines a live OR result, two subtraction-leaf calls,
swapped first arguments, computed second arguments, and a final XOR. The
ordinary case exits 3; the full-width wrapping case exits 255.

## Log

- 2026-09-19: Implemented bounded expression reflection, preserved-register selection, and register facts composed through reusable callee contracts. The executable passes ordinary and full-width wrapping inputs (statuses 3 and 255), using one summary twice. Focused tests reject stale source plans, incorrect register values, non-selected callees, excess calls, and unsupported register pressure. Full-suite final result pending.
- 2026-09-19: Final plain scripts/test passed: 2823 passed, 0 failed, 5 ignored. Both new executable inputs passed under unchanged limits (native_composition: 56.5 CPU-s against the 300-second rail), along with the original forwarding, stack-local, reusable-summary, and scaling gates. No kernel or proof-library changes. General spills, call graphs, and reusable caller ABI contracts remain owned by x86-calls-stack-frames; this bounded milestone is complete.
