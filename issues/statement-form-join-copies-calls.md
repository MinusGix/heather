---
title: A statement if/match that assigns several locals copies its body, calls included, once per local
status: closed
labels: [elaboration, imperative]
area: language
created: 2026-11-12
updated: 2026-11-12
---

The statement lowering joins each assigned local separately
(`crates/syntax/src/imperative.rs`, the `#stageN` lets;
docs/sequencing-surface-design.md §12 states the cost as "one condition copy
per assigned local per `if`"). It copies the whole form, not the condition:
a call in a branch is written once per local the form assigns.

```heather
fn Counter::fill_sum(mut self c: Counter, m: Nat) → Nat decreases m {
    let mut s = 0;
    if 1 <= m {
        c := Counter(c.n + m, Cons(m, c.log));
        let k = c.fill_sum(m - 1);
        s := k + m;
    }
    s
}
```

`c` and `s` are both assigned, so the `if` becomes two matches, `#stage1`
computing `c` and `#stage2` computing `s`, and each holds the self-call.
Under `decreases` that is two obligation sites (`?dec1`, `?dec2`: an `on`
for one leaves the other to `omega`), and evaluating the result calls the
recursion twice per level, so the value is exponential in the depth where
the source is linear. The same holds for any expensive call in such a
branch, recursive or not.

This is the shape a measured `mut self` loop that returns a value has to
take today (a receiver changes only in statement forms;
[[decreases-self-parameter]]'s log), so it is the one the SHA-256
context's methods would reach.

Directions, not decided: bind each branch's work once and project the joins
from it (a join record or the `Mutated` nesting the loop lowering uses,
§5.2's `\0state`), at the cost §2 named, that proofs project; or hoist the
branch's `let`s that every join reads into one shared binding per branch.

Done when: the example's `if` holds one call, with a probe that counts the
obligation sites (one `on ?dec1` discharges the method).

## Log

- 2026-11-12: Closed with the first direction. `crates/syntax/src/imperative.rs`
  joins a statement form once, whatever it assigns: each arm ends in the
  state `Mutated(v₁, Mutated(v₂, …))` the carrier loop already threads
  (`state_expr`), bound at `#stageN : Mutated<TypeOf(v₁), …>`, and the
  locals are read out with `.after`/`.value` (`state_reads`). One local is
  joined directly as before. Probe `fill_once` in
  `lib/_tests/std/core/decreases_unfolding_tests.hthr`: the example's
  `if` owes one obligation, so `on ?dec2` names no goal.
  docs/sequencing-surface-design.md §3, §12 and §14 item 3 amended. The
  whole library re-elaborated under the exact image policy with no proof
  needing the per-local shape.
