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
  (`docs/native/native-lexer-crypto-roadmap.md` §5) therefore compiles the round as
  a loop body over an array state first ([[rt-fixed-arrays-and-tables]],
  [[sha2-compress-native]]) and treats the unrolled form as waiting on this
  issue.
- 2026-11-10: The scanner's automaton (`lib/lang/lexer/lexer_scan.hthr`) is the first table-shaped code certified, and this cost set its layout: a family of states is one function of about sixteen arms, because a function of twenty-one arms (`step_symbols` before it was split in two) failed with `…_native_scanned_0: OutOfFuel`. Twenty-three families certify, each in its own program. A function a little past that size hits memory before fuel ([[compile-x86-certificate-memory]]). Logarithmic marks would let a family be the natural one (all the symbol states together) and are the first of three things between the automaton and one compiled `scan_step` ([[runtime-generator-program-size]]).
- 2026-11-10: The scan is no longer the first limit of a function, by two changes; the issue stays open for the exponent that is left.

  - **The kernel compared the verdict's type a δ-step at a time** ([[type-conversion-one-sided-delta-steps]]). A scan statement is `scan(…).IsTrue()` by `trivial`, and its type was unfolded one step per round with the pending spine replayed each time. One run now: the same statement fell from 342k steps to 100k (and from 1.4 s to under 0.1 s), which is what `scan(…) = True` by `refl` had cost all along. This was most of what the tables above measured.
  - **Marks under a bound.** `Marks` is `Bitmap` or `Under(top)`: every id under `top`. The verified lowering names its values in rising order, so a scan under `Under` marks and tests with one accelerated comparison whatever the id, and `Function::scan` tries it before the bitmap (`scan_from`; soundness is `Function::scan_from_evaluable` for either).

  Measured after both (cloud box, width one, one function of constants under comparisons): a 16-arm chain scans in 100k steps, a 24-arm chain in 173k, a 40-arm chain in 370k, a 64-leaf tree in 742k. That is between linear and quadratic in the function's size (an exponent of about 1.4 on the chains), where the unary bitmap was quadratic with a larger constant. In every case the function's emission statement costs more and fails first ([[native-function-emission-one-statement]]), so this is the second limit of a function, at about half again the size the first allows. The scan is also against a table of arities now (`program_scan_at`), so a caller's statement does not force its callees' code ([[compile-x86-certificate-memory]]).

  Left for this issue: where the remaining superlinear part comes from (the joins of a conditional's marks, or `calls_fit` and the mentions lists being rebuilt per level), measured once emission no longer hides it.
- 2026-11-10: From the emission round ([[native-function-emission-one-statement]]): the scan compares ids too, so the kernel reading a written counter as a run ([[succ-chain-numbers-fold-unary]]) and `Nat::eq_dec` deciding by `same` moved it without touching it. A 100-leaf tree's `scanned_0` is 0.40M steps, where the 64-leaf tree's was 0.74M: about a third of the cost per node. It is half of the same function's emission and still not the first limit.
