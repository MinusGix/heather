---
title: Comparing numerals past 2^96 costs their value over 2^63
status: open
labels: [kernel,performance,numerals,floating-point]
area: kernel
milestone: [math-float]
created: 2026-10-21
updated: 2026-10-21
---

`Nat::leb` and `Nat::sub` on two closed numerals run out of fuel once the
numbers pass about `2^96`, however close together they are. Found while
evaluating floating-point roundings at binary32 sizes (float-arith,
`docs/floating-point-design.md` §14): the half-unit count of an ordinary
binary32 value is near `2^150`, so no binary32 rounding computes by `refl`,
through either `round_dyadic` or `round_rat`.

## Reproducer

```heather
import logic; import bool; import nat;
theorem ok(): (79228162514264337593543950336).leb(79228162514264337593543950337) = True { refl }   // 2^96: checks
theorem no(): (158456325028528675187087900672).leb(158456325028528675187087900673) = True { refl } // 2^97: OutOfFuel
```

The same holds when both sides come from `Nat::pow(2, k)`, and for `3^70`
(about `2^111`). `half` of such a number is fine; only the comparison and
the subtraction fail.

## Why

A numeral past `u64::MAX` evaluates to a run program built by doubling
(`docs/wide-numerals-design.md` §2): shared `u64` runs under a composition
DAG. `leb` and `sub` are synchronous folds, so their application cancels the
two programs' common prefix with `ContextProgram::cancel_matching_prefix`
(`crates/kernel/src/value/program.rs`). Bisimilar DAG fronts are skipped by
node pairs, but two numbers built by different routes are not bisimilar node
for node, and the fallback walk visits run fragments one at a time, each at
most `2^63`. Its cost is the value divided by the fragment size, so the
inspection budget is gone shortly after `2^96`.

## Proposal

A representation change with an adequacy argument, in the policy's first
kind (`crates/kernel/DESIGN.md`, acceleration policy): when both programs are
closed runs of `Succ`, cancel by their counts as numerals (`Numeral` already
has the limbs), one subtraction of naturals rather than a walk. Or count runs
with an unbounded count so the walk visits `O(bits)` fragments. Either needs
the differential oracle and a `scripts/perf ab` pair, since the cancellation
sits on the evaluator's hot path.

## Done when

The reproducer's second theorem checks, and a binary32 rounding of a literal
(say `round_rat` of `1/3`, or `round_dyadic` of a binary32 sum) computes by
`refl` in the float-arith tests.
