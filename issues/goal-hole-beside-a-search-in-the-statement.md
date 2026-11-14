---
title: A goal hole in a body whose statement names a search is an internal error
status: open
labels: [elaboration,goals,diagnostics]
area: language
created: 2026-11-13
updated: 2026-11-13
---

```heather
fn word_below(i: BitVec(64), inside: i.toNat() < 64 := bv_omega) → BitVec(64) { i }

fn climb(acc, j: BitVec(64)) → BitVec(64)
    decreases (48 - j).toNat() {
    if h: j < 48 { climb(acc + word_below(j + 16), j + 1) } else { acc }
}

theorem climb_step(acc, j: BitVec(64), h: j < 48): climb(acc, j) = climb(acc + word_below(j + 16, inside := bv_omega), j + 1) {
    trans(climb_unfold(acc, j), ?)
}
// internal: more goals than the pre-count reserved
```

The statement gives a parameter's proof by a search (`inside := bv_omega`) and the body leaves a goal `?`. The report should be the goal with its statement; instead the goal arena runs out of the slots counted for the declaration. Seen 2026-11-13 while writing a probe for PR #607 (the probe was written another way); not reduced further, so the search in the statement may not be the needed part.

## Done when

The declaration above reports its open goal, with a probe in `lib/_tests`.

## Log
