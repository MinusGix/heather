---
title: A branch whose test reads the object's length (`if h: j < xs.len()`)
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

From [[ownership-site-facts-into-the-checker]]. The checker's branch test is `Cond = Le(a, b)` over atoms, words read in the environment. A source branch whose test reads the object (`if h: j < xs.len()` in the fifth experiment's `hop_if`) has no `Cond`: `hop_if`'s probe discharges `hop`'s residuals from the `if`'s evidence, but `hop_if` itself is not a checker body. A test over the object's length is the common guard before an unchecked read (the arena's `read` called under `if h: i < heap.len()`).

## Wanted

A `Cond` reading the place's length (`a < |x|`), read in the meaning as the current value's length and in the run as the reference's (`Sim.on.len` makes them agree; a lending function has no owner to test), and `hop_if` as a checker body with its pin, discharge and safety.

## Done when

`hop_if` is a checker body with `hop_if_reflects` by `refl` and its safety from `check_owned`.

## Log

- 2026-11-25: Not a further round on `call_check.hthr` (docs/language/ownership-design.md §20): the experiment module is not extended again. This is a requirement on the checker built once over the fixed interfaces (§20.6) and is closed by that build.
