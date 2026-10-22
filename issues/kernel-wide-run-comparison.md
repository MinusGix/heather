---
title: Comparing numerals past 2^96 costs their value over 2^63
status: closed
labels: [kernel,performance,numerals,floating-point]
area: kernel
milestone: [math-float]
created: 2026-10-21
updated: 2026-10-22
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

## Log

- 2026-10-22: closed. Three changes, all representation or strategy, no new
  semantic case (`crates/kernel/src/value/program.rs`):
  1. **Lengths on the nodes.** `ContextProgram::Compose` carries `len` (a
     `Numeral`) and `uniform` (the one context every run below repeats, when
     there is one), filled in by `ContextProgram::compose`, the only
     constructor. `repetition_count_up_to` is now a read, not a walk.
  2. **Uniform fronts are never opened.** The cancellation cursor makes a
     uniform piece its front whole, run or composition alike, and absorbs
     following pieces of the same context while it is the shorter side; two
     fronts cancel by one subtraction of lengths, and only the longer one is
     cut, along one path (`drop_prefix`). For `Nat` every program is uniform,
     so comparing two numbers of `b` bits costs `O(b)` inspections however
     they were built, and two numbers of different lengths are refuted at
     once. Bisimulation remains for mixed-context programs (and filters on
     length). The differential oracle is a unit test against expansion over
     random small programs with mixed contexts and sharing.
  3. **Compaction.** An affine fold iterated over a run builds its result's
     graph from the input's, and a chain of `half`s grew a 150-bit number to
     ~4,700 nodes; `AffineTree::iterate` now rebuilds an increment from its
     count in the literal shape (`ContextProgram::of_count`, which
     `nat_lit_program` now calls) when its graph is past two nodes per bit.
  Library: `Format::pick` (the exponent search in `float/round.hthr`) carries
  its shift and its bound, so it costs `e` halvings and one `F.top()`, not
  `e²` halvings and `e` powers; `Nat::shr_succ_half` is the lemma it needed.
  The float-arith tests now evaluate binary32 sums, products and `round_rat`
  toward zero and toward `-∞` by `refl`. Rounding to nearest of a *computed*
  half-unit count at binary32 is still over fuel, for a reason that is not
  comparison: [[computed-argument-reevaluated-in-rounding]].
