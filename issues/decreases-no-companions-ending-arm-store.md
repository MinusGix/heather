---
title: No ext or irrel for a decreases function whose ending arm stores through mut self
status: open
labels: [frontend,elaboration,termination]
area: language
created: 2026-11-13
updated: 2026-11-13
---

A `decreases` function with `mut self` whose **ending** arm (the one with no self-call) stores into the record gets no `f::ext` and no `f::irrel`. Found making a loop of a laid record a `runtime fn` (PR #551): the generator builds the loop's theorem from those companions and refuses the function by name.

```heather
laid(endian := BigEndian) record Tally { count: u64, total: u64 }

// No companions: the store is in the arm that ends.
fn Tally::late(mut self t: Tally, i: u64) → u64
    decreases (8 - i).toNat() {
    if h: i < 8 {
        t.late(i + 1)
    } else {
        t.total := i;
        i
    }
}

// Companions made: the store is before the self-call, or there is none.
fn Tally::early(mut self t: Tally, i: u64) → u64
    decreases (8 - i).toNat() {
    if h: i < 8 {
        t.total := i;
        t.early(i + 1)
    } else {
        i
    }
}
```

Both check, and `lookup("Tally::late::ext")` is refused where `Tally::early::ext` is found. The shape is a sibling of [[decreases-mut-call-statement-companions]] (closed: a `mut self` call statement before the self-call) and [[decreases-no-companions-nested-match-calls]]; here the arm that is declined has no recursion in it at all, so the walk that emits the companion should have nothing to follow there. Not looked into further.

Meanwhile a loop stores before its test or in a caller (`lib/_tests/native/runtime/runtime_held_loop_tests.hthr`, `Tally::late` under its `expect-error`).

Done when: `Tally::late` has its companions, and the probe's `expect-error` becomes a loop that compiles.

Related: [[runtime-record-function-limits]], [[decreases-unfolding-equations]].
