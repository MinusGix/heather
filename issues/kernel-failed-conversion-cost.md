---
title: Reject false large conversions without spending a successful proof's budget
status: open
labels: [kernel,conversion,performance,diagnostics,testing]
created: 2026-09-03
updated: 2026-09-09
---

The full x86 `ControlRegion` honesty control first forged a semantic execution
endpoint. The proposition was false, but conversion explored the large shared
machine/proof structure for roughly 150 seconds and consumed the ordinary fuel
budget before reporting failure. Replacing it with the focused false equality
`MovRR(R9, Rsi) = MovRR(R8, Rsi)` keeps the test useful and rejects quickly,
but only avoids the underlying behavior.

Minimize and attribute false conversions whose mismatch lies behind large
dependent applications, projections, or transparent definitions. The goal is
not to make every negative constant-time; it is to prevent an early or shallow
semantic disagreement from requiring normalization of unrelated proof/state
payloads. Candidate levers must preserve the deterministic fuel discipline and
must not introduce speculative rollback or accept incomplete left-biased
application comparison.

## Acceptance

- A reduced kernel-level family varies mismatch depth and shared payload size,
  reporting reduction, value construction, comparison, fuel, and allocation.
- The original forged x86 endpoint (or a faithful small reproducer) returns
  `NotConvertible` comfortably inside the ordinary rail rather than
  `OutOfFuel` after work comparable to the whole successful certificate.
- Positive large conversions and the generated fold/tabulate oracle controls
  retain their existing judgments and fuel bounds.
- Any shortcut is justified by the conversion rules and carries adversarial
  controls where the apparent early mismatch later converts after unfolding.
- Diagnostics distinguish a genuine mismatch from exhausted resources.

## What it assumes from elsewhere

- **[[application-annotation-sharing-cost]]** owns residual cost in successful
  stored-annotation comparison. This issue owns the asymmetric failed path.
- **[[generated-term-oracle-controls-not-convertible]]** establishes why an
  incomplete inferred-Π shortcut or fuel-refunded fallback is not acceptable.

## Log

- 2026-09-09: New member of the family from [[bitvec-width-bounded-defaults]]: bitvec::add(64, x, y) = bitvec::sub(64, x, y) over open x, y is NotConvertible at width 8 but OutOfFuel at width 64 — both are ripples agreeing on every sum bit and differing only in the column carry (carry_majority vs borrow_next), so the disagreement sits behind 64 columns of shared structure. Pinned as add_and_sub_differ in crates/elab/tests/lib_std_bitvec.rs; the stale-source control in function_ir_x86.rs accepts either refusal until this is fixed.
