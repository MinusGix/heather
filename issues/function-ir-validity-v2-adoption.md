---
title: Adopt the compact FunctionIR validity boundary without rebuilding RegionValid
status: open
labels: [compiler,proofs,performance,function-ir,design]
created: 2026-08-31
updated: 2026-08-31
---

[[function-ir-validity-environment-scaling]] produced a successful
`RegionValidV2` prototype: stable-ID directory facts, schedule ranks, and
shared generated stages validate a 100-node graph at ordinary test scale.
Existing `CheckedRegion` clients still package the original quadratic
`RegionValid` relation.

The adoption path must not prove V2 validity by reconstructing the old
freshness/linear-lookup tree for every node; that would preserve correctness
while losing the reason V2 exists. Decide whether to replace the existing
boundary directly or introduce a temporary common checked-region interface.

## Acceptance

- Downstream semantics and lowering consume the compact validity boundary.
- Existing `add64` and both `sum4` schedules retain their theorems and x86
  lowering artifacts.
- The in-language reference validator remains available as a specification or
  fallback without being rerun by ordinary compiler output.
- No compatibility theorem reconstructs a quadratic `RegionValid` certificate
  on the fast path.
- The experimental `V2` naming is removed or given an explicit compatibility
  lifetime once the boundary is selected.
