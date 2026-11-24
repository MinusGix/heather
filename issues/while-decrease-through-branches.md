---
title: A while's decrease is not found when the measure is assigned through an if
status: open
labels: [loops,omega,elaborator]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

A `while` whose measure variable is assigned through a branch is refused
with "this pass of the loop must decrease the measure", though every arm
decreases it. Found writing a hash table's probe loop
(`Bytes::port_set_put`, `lib/_tests/native/runtime/runtime_ports_tests.hthr`).
Minimal, with no `runtime fn` involved:

```heather
import runtime;

// Passes: the new value is `left - 1`.
fn dec_one(x: u64) → u64 {
    let mut left = x;
    while 0 < left decreases left.toNat() { left := left - 1; }
    left
}

// Refused: an `if` statement that assigns in each arm.
fn dec_arms(x: u64) → u64 {
    let mut left = x;
    while 0 < left decreases left.toNat() {
        if left = 5 { left := 0; } else { left := left - 1; }
    }
    left
}

// Refused as well: an `if` expression as the new value.
fn dec_tail(x: u64) → u64 {
    let mut left = x;
    let mut r: u64 = 0;
    while 0 < left decreases left.toNat() {
        r := r + 1;
        left := if left = 5 { 0 } else { left - 1 };
    }
    r
}
```

The search's report shows the new `left` and the old `__loop_s.left` as two
unrelated atoms (CutSat's model sets both to 1): the obligation
(`crates/elab/src/declarations.rs`, `elab_loop_family`, which rewords the
`omega`/`bv_omega` failure) reaches the decision procedure with the pass's
new state as a `match` on a `Bool` that neither `omega` nor `bv_omega`
splits.

## Fix

Split the obligation at each `Bool` match (an `if`) in the new measure
before the search, each arm with its test as a hypothesis, as Lean's
`decreasing_tactic` does with `split`. The same split serves the measure of
a recursive function whose argument is an `if` (`crates/elab/src/measure.rs`);
check whether it shares the route.

## Done when

`dec_arms` and `dec_tail` elaborate, `port_set_put` in the ledger passes
the elaborator (it may then stop at the generator's own refusal, which the
row's expectation names), and a control whose one arm does not decrease
(`if left = 5 { left := left; }`) is still refused.
