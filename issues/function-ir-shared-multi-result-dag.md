---
title: Share DAG work across simultaneous physical results
status: open
labels: [compiler,function-ir,x86]
created: 2026-09-20
updated: 2026-09-20
---

Physical multi-result selection now lowers a dependency slice for each result,
protecting completed result registers. This is general and locally certified,
but can recompute common nodes and reject avoidable register pressure.

Extend ordinary DAG selection to retain multiple live results in a single pass
and emit all placement proofs over that shared instruction sequence. Preserve
explicit output maps and the existing scalar API. Test shared subexpressions,
passthrough results, outputs used by later outputs, comparison-bit results,
and register pressure; reject a certificate that overwrites an earlier result.

Build on [[function-ir-recursive-structured-lowering]]. General edge copies and
parallel-copy cycles remain in [[function-ir-x86-join-placement]]. This is an
allocator/certificate improvement, not an application-specific lowering path.
