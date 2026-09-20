---
title: Preserve shared let values and call results in source-call lowering
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Problem

The bounded source-call selector reflects the elaborated caller as an expression
tree. Surface `let` bindings have already been expanded, so using a computed
binding twice can emit two computations or two calls. For example,
`let result = leaf(left, right); bitvec::add(64, result, result)` should call
`leaf` once and reuse the result. Today the expanded occurrences also consume
the four-call limit independently.

## Acceptance

- Preserve or recover a shared value graph from resolved elaborated source.
- Emit one call for a shared call result and reuse its checked result fact.
- Track last uses and live values across calls; report unsupported register
  pressure or spills explicitly.
- Keep distinct argument pairs distinct, and retain source/refinement and
  fetched-execution checks. Do not infer sharing from surface names alone.
- Test a call result used twice, shared arithmetic, different call arguments,
  and stale value/argument evidence. Count actual CALL instructions and summary
  applications, alongside native execution results.

## What it assumes from elsewhere

- [[x86-source-call-composition]] supplies the bounded expression selector and
  reusable leaf-contract composition.
- [[x86-calls-stack-frames]] owns broader calling and frame profiles.

## Log

- 2026-09-19: Recovered structural sharing from the resolved caller expression before instruction selection. Distinct DAG consumers determine last uses; shared arithmetic and call results retain their registers across later calls. The four-call limit now counts distinct argument-expression pairs, while the 64-expanded-node reflection guard remains explicit.

  The new sharing fixture contains five expanded call occurrences but selects two actual encoded CALL instructions and five caller additions. It checks both selector profiles, generic source/ABI proofs, and omitted-clobber refusal; its native test also requires exactly two leaf-summary applications and one outer-summary application. Focused call tests pass (8/8); full-suite verification is running.
- 2026-09-19: Final plain scripts/test passed: 2830 passed, 0 failed, 5 ignored. The shared-value ELF executed with status 50 and exactly two leaf-summary applications; both selector profiles, generic proofs, and refusal controls passed. Closed.
