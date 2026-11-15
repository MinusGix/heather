---
title: A proof by `if h:` over a measured call's `.after` is accepted by the elaborator and refused by the kernel
status: closed
labels: [elaborator, matching]
area: elaborator
created: 2026-11-15
updated: 2026-11-15
---

Found by the end-to-end sort demo: a theorem about a measured `mut self`
method's `.after`, proved by `if h:` (or `match h: decide_bit<…>()`) on
the method's own test, was refused by the kernel with no surface spelling,
even with `refl` in both arms:

```
theorem fill_down_if(c: Counter, m: Nat): Counter::fill_down(c, m).after.n = Counter::fill_down(c, m).after.n {
    if h: 1 <= m { refl } else { refl }
}
error: the kernel rejected `fill_down_if`: NotConvertible. … the kernel refused `a`, which has type `x = True`, where `leb(1, m) = True` is expected
```

## Log

- 2026-11-15: Fixed (branch claude/project-thread-h1d10i). The motive
  synthesis' reduced rung (§4.4) abstracted the test where the unfolded
  body is stuck on it and in its convoy, and missed a type the body uses
  the evidence at, so the motive was ill-typed for every arm. A motive
  built by a rung that reduces the goal is now type-checked under `z`
  before it is used (`MotiveSynthesisElab::motive_well_formed`), and one
  that fails falls through to the next rung and finally to the goal as
  written; the arms then use the evidence against the function's
  equations. docs/elaborator/goal-motive-synthesis-design.md §4.6; probes
  in lib/_tests/std/core/match_motive_checked_tests.hthr. Related:
  [[match-arm-accepted-against-unspecialised-goal]] (a different cause,
  its message).
