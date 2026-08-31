---
title: Replace FunctionIR validity with the compact directory and rank model
status: open
labels: [compiler,proofs,performance,function-ir,design]
created: 2026-08-31
updated: 2026-08-31
---

[[function-ir-validity-environment-scaling]] produced a successful
`RegionValidV2` prototype: stable-ID directory facts, schedule ranks, and
shared generated stages validate a 100-node graph at ordinary test scale.
Existing `CheckedRegion` clients still package the original quadratic
`RegionValid` relation. There is no compatibility constituency for that
representation: the compact model should replace it directly.

Delete the old freshness/linear-lookup validator and generator rather than
maintaining two validity APIs or introducing a common compatibility interface.
The in-language algorithm remains useful only as design history; ordinary
compiler output has no reason to construct the inferior proposition.

## Acceptance

- Downstream semantics and lowering consume the compact validity boundary.
- Existing `add64` and both `sum4` schedules retain their theorems and x86
  lowering artifacts.
- The old in-language validator, quadratic proposition, and quadratic Rust
  generator are removed.
- No compatibility theorem reconstructs a quadratic `RegionValid` certificate
  on the fast path.
- The experimental `V2` naming is removed: the compact relation is
  `RegionValid` and the compact generator is `generate`.

## Language performance debt exposed by the replacement

- **[[frontend-large-proof-composition-cost]]** owns making monolithic proof
  spelling retain the sharing currently supplied by generated stages.
- **[[named-argument-checking-context-loss]]** owns the expected-type failures
  that force several generated helper calls to spell inferable data.
- **[[nat-order-large-run-comparison]]** owns the catastrophic normalization
  found when otherwise tiny directory certificates use IDs near `u64::MAX`.

Neither blocks replacement: staged output is correct and fast enough today.
