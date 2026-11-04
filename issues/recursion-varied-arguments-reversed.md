---
title: A self-call's varied arguments were applied to the ih in reverse
status: closed
labels: [recursion,elaboration,soundness-of-meaning]
area: language
created: 2026-11-04
updated: 2026-11-04
---

A miscompile on master 409f430e: when the decreasing parameter came third or
later, the varied arguments before it reached the ih in reverse order.
`elab_self_call` moved the decreasing argument to the front with
`order.swap(0, decreasing)`, which also moved the first argument to the
decreasing argument's slot, so for `f(a, b, n)` the ih saw `b, a`:

```
fn sw(a, b, n: Nat) → Nat { match n { Zero => a, Succ(k) => sw(Succ(a), Succ(b), k) } }
// sw(0, 10, 1) evaluated to 11, not 1.
```

The kernel accepted it (the swapped arguments had the same type), so only
evaluation or `--review`'s meaning check could see it. Found while making
recursion at the top the default ([[recursion-at-top-nat-default]]), where
every other explicit parameter is generalized and `p(a, n, fuel)`'s
`p(a, n, Succ(f))` stopped unfolding to its source.

## Log

- 2026-11-04: fixed by rotating the decreasing argument to the front
  (`order[..=decreasing].rotate_right(1)`); probes `sw_varied` (plain
  lowering, a `List`) and `three_varied` (at the top) in
  `lib/_tests/std/core/recursion_at_top_tests.hthr` pin the values by `refl`
  (both fail without the fix).
