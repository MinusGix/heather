---
title: rewrite misses a class member called at a concrete carrier when the law is stated at a child class
status: open
labels: [tactics, classes]
area: tactics
created: 2026-11-25
updated: 2026-11-25
---

`ExactClone::clone_eq<A: ExactClone>(x: A): A.clone(x) = x` (`lib/std/core/clone.hthr`) states its left side through the child dictionary, so its head is `ExactClone.clone` (dispatch reads through the upcast, `docs/language/classes/traits-named-upcast-design.md`). At a concrete carrier, `x.clone()` with `x: u64` resolves the member's owner `Clone` and elaborates to `Clone.clone(x)`. The two convert, but `rewrite` looks for an occurrence by head ("a subterm with the left side's head that converts to it, as written or one unfolding of it") and refuses:

```
`rewrite`: the goal `toNat(Clone.clone(x)) + y = toNat(x) + y` does not mention the equation's left side `ExactClone.clone(x)`
```

`simp_only(ExactClone::clone_eq)` and a simp set naming it rewrite the same goal, and `rewrite` works at an open carrier (`A.clone(x)` under `A: ExactClone`), so the probes use those (`lib/_tests/lang/facts/copy_tests.hthr`, `clone_under`, `clone_under_word`). Every law of a child class (`CommMonoid`'s `comm` over `Monoid`'s `op` at a concrete carrier) would meet the same.

## Done when

`rewrite(ExactClone::clone_eq(x), refl)` proves `x.clone() + y = x + y` at `x: u64`, by treating a class projection read through an upcast and the ancestor's projection as one head.
