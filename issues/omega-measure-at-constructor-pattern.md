---
title: omega treats a measure applied to a constructor pattern as an opaque atom
status: open
labels: [proofs,omega,elaboration]
created: 2026-09-05
updated: 2026-09-05
---



Found by the mutual-recursion design pass (2026-09-05,
docs/mutual-recursion-design.md §7), reproducing on a *single* `decreases`
declaration: `fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs)` recursing
on the tail is refused — `list_len(t) < list_len(Cons(h, t))` "was not proved
automatically (`omega` got stuck: Omega could not spell a natural expression)".
`list_len(Cons(h, t))` is an opaque atom to the reflection rather than
`Succ(list_len(t))`, so the default closer fails on the single most common
measure obligation there is. Every existing `decreases` test discharges such
sites by hand (`merge`'s `succ_add_le`, `runs`'s `drop_eq_le`), which is why
it was invisible. Lever: reduce an atom to whnf (the value-domain probes of
`docs/…whnf…`, see [[elaborator-whnf-probes-on-computing-types]]) before
reflecting it, so a measure at a constructor pattern steps once. This is what
stands between the showcase parser and `omega`-only obligations.

## What it assumes from elsewhere
- **[[termination-measures]]** owns the obligation statement. Assumed here:
  only that the obligation is stated at the pattern-refined measure.
