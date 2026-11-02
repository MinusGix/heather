---
title: A recursion under a branch on a parameter its calls change skipped the branch
status: closed
labels: [elaboration,correctness,recursion]
area: language
created: 2026-11-02
updated: 2026-11-02
---

A structural recursion under a branch on a parameter its self-calls change
compiled to a different function than the source:

```
fn v2(d: Nat, xs: List<Nat>) → Nat {
    if d = 0 { 0 } else { match xs { Nil => 7, Cons(x, t) => v2(x, t) } }
}
// source: v2(1, [3, 0, 4]) = v2(3, [0, 4]) = v2(0, [4]) = 0
// compiled: 7 — `refl` at 0 was refused only by the kernel, and at 7 it checked
```

The structural lowering compiles the recursion at the `match` on `xs` and
generalizes `d` into its motive, so a self-call is the `match` alone at the
new `d`: the branch above it is decided once, by the top call. The planner
already refused a recursive `match` under a branch on the *decreasing*
parameter (`spine.contains(&dec)`), but not on a *varied* one. Found while
working [[recursion-outer-match-takes-guard-without-descent]], which would
otherwise have let `match d { …, Succ(_) => match xs {… f(x, t) } }` through
with the same wrong meaning; on master the computed-scrutinee and `if`
spellings had it already.

## Resolution (2026-11-02)

`recursion::plan` refuses a recursive `match` whose enclosing branch reads a
parameter its self-calls vary ("sits under a branch that depends on `d`,
which its recursive calls change"), as `Misplaced`, refused at the self-call.
The planner's `reads` now also looks inside type arguments (`decide_bit<d =
0>()`), which `for_each_child` skips, so a computed scrutinee's dependencies
are seen. Probes in `lib/_tests/std/core/recursion_case_split_tests.hthr`
(the `match`, `if` and `decide_bit` spellings, and the unchanged-parameter
control).

Lowering such a declaration by a measure instead, as the stale-let case does
([[recursion-let-reads-changing-parameter]]), would accept it; not done here,
since a branch can always move inside the arms.
