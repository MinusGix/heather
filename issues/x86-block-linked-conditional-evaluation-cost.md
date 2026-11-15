---
title: x86_64_block's LinkedConditionalDecodes/Layout are a million evaluator steps each, the corpus's heaviest declarations
status: closed
labels: [x86,performance,kernel]
area: heather-in-heather
created: 2026-09-23
updated: 2026-10-24
---

The two heaviest declarations in the whole perf corpus are x86 library
declarations, paid on every cold build of the x86 library (after each
compiler change, and on any edit to it):

| item | total | gate | lower | eval steps | misses |
|---|---|---|---|---|---|
| `x86_64_block::LinkedConditionalDecodes` | 1,244 ms | 72 % | 27 % | 1,508,504 | 380 |
| `x86_64_block::LinkedConditionalLayout` | 1,212 ms | 56 % | 44 % | 971,065 | 373 |

(snapshot `perf/snapshots/2026-09-23T140408Z-local.json`, `reused_callee`
cold, width one.) `x86_64_block` is 4.1 s of the library's cold 15.5 s; these
two are 60 % of it.

Shape: few misses and ~0.6 µs per step, so the gate time is genuine
evaluation — a million-plus steps, likely decoding or laying out concrete
bytes by computation. `lower` at 0.3–0.5 s is unusual for a single
declaration (the next largest `lower` in the run is 27 ms).

Question to answer before any fix: are these checked by evaluating a closed
decode over a concrete byte table (so steps scale with the table), and is the
`lower` time the same term being lowered? Probe with `--cache --only
x86_64_block::LinkedConditionalDecodes --timings` over a replayed prefix.

Trigger: only if the x86 library's cold check becomes a bottleneck (edits to
`x86_64_block`, or the suite's first native build after a compiler change).
Not worth a round by itself today.

## Log

- 2026-09-23: 2026-09-23: the fast lane's critical path is the same shape in the guarded-read test — [[fast-lane-heaviest-declarations]].
- 2026-10-24: Not planned: what this issue is about was deleted in burn B2 (docs/native/native-program-logic-design.md §3.2). The verified `compile-x86` path (`function_ir_compile`, `compiled_returns`) replaces it; the last commit with the old code is `82521ea`.
