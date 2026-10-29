---
title: Structural recursion takes the nearest match on a parameter as its guard
status: open
labels: [frontend,recursion,elaboration]
area: language
created: 2026-10-29
updated: 2026-10-29
---

The structural recursion check takes the nearest enclosing `match` on a
parameter as the recursion's match, so a self-call under an inner case
split on *another* parameter is refused as not descending:

```
fn walk(d: Nat, n: Nat) → Nat {
    match d { Zero => 0, Succ(k) => match n {
        Zero => walk(k, n), Succ(_) => Succ(walk(k, n)) } }
}
// error: recursive call to `walk` must descend: argument `n` has to be `_`,
//        the predecessor bound by the enclosing `match`
```

`d` descends (`k` is its predecessor) and `n` is passed unchanged. Writing
the inner split on a non-variable (`match Nat::add(n, 0)`) or in a helper
is accepted. Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]).
Memory has a neighbouring note from the measure-loops round (2026-10-26):
"a theorem whose recursion is inside a nested `match` under λ/let says
'applied to too many arguments' — put the match at the top".

[[fn-recursion-means-the-function]] owns spellings that are refused because
their compiled meaning would differ; this one would compile to the same
recursor on `d`, so it is a guard-selection gap, not a meaning gap.

## Acceptance

- `walk` checks, and `walk(24, 3) = 24` by `refl`.
- A self-call that descends neither match is still refused, naming the
  matches it tried.
