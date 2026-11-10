---
title: Mark FunctionIR ids in time logarithmic in the id, not linear
status: open
labels: [native,function-ir,perf]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-07
updated: 2026-11-10
---

`program_scan` (`lib/native/function_ir/function_ir_eval.hthr`,
[[function-ir-evaluable-quadratic]]) checks a function's evaluability in one
pass, but its marks are a bitmap indexed by unary ids: marking or testing id
`k` walks `k` cells. A function's cost is therefore the sum of the ids it
mentions, which grows with the square of its size (ids are allocated
increasingly, so the largest is about the function's size).

Measured on the cloud box, kernel steps of one declaration, at width one:

| function | mentions | sum of ids | `scan` steps | forcing the code alone |
|---|---|---|---|---|
| lexer `step_full` | 109 | 1699 | 303k | ~50k |
| lexer `class` | 85 | 1142 | 210k | ~32k |
| `byte_class_pair` (14-arm `byte_class` + caller, `lib/_tests/native/runtime`) | | | 553k | |

So about 150 steps per unit of mentioned id, against the 2^20 fuel per
declaration: a function about twice `step_full`'s size runs out again. The
certificate already checks one function per declaration
(`program_scan_drop`), so the limit is the largest function, not the program.

Two observations from probing (`--timings`, probe theorems over the
reflected program):

- Marking alone (`marks_add_all` over `step_full`'s mentions) is about 56k
  steps beyond forcing the code; with the scan's interleaved tests and the
  conditionals' joins, the marks cost about 200k. The structure is lazy
  (`marks_add` rebuilds a prefix whose tail and `||` cells are forced on
  demand), so the bounded force cache may be re-forcing evicted cells.
- `Nat::leb`, `same`, `half`, `sub`, `min`, `max` are run-accelerated (one
  comparison of six-digit literals is ~49 steps), while `eq_dec`/`differs`
  and any structural walk pay per unit (~25 steps).

## Done when

A function's scan costs `O(mentions · log(id))` (or the per-unit constant
is cut enough that a function several times `step_full`'s size certifies),
with `program_scan_evaluable` kept as the theorem the certificate cites.
Candidates: marks as a binary trie keyed through the accelerated `half` and
a parity test (`O(log id)` levels at a constant each); or marks kept from
the frontier down, so the usual fresh write and recent read are O(1) and
only join ids walk.

## Log

- 2026-11-10: A compression function is the first body where this cost decides the
  design: sixty-four (or eighty) rounds unrolled mention ids in the
  thousands, and the scan pays the sum of them in unary. The roadmap
  (`docs/native-lexer-crypto-roadmap.md` §5) therefore compiles the round as
  a loop body over an array state first ([[rt-fixed-arrays-and-tables]],
  [[sha2-compress-native]]) and treats the unrolled form as waiting on this
  issue.
