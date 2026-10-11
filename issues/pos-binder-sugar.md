---
title: Pos<A> binder sugar: a value plus an inferred positivity hypothesis
status: open
labels: [frontend,syntax,elaboration,stdlib,ergonomics]
created: 2026-10-10
updated: 2026-10-10
---

`x: Pos<A>` in a binder elaborates as `x: A, x_pos: 0 < x := infer`, for any
`A` with `0` and `<` designated. Nothing is wrapped: callers pass a plain
`A` and positivity is found by [[infer-proposition-evidence]]. Design:
`docs/positivity-evidence-design.md` §6 B.

Three positions, in order:

1. **Parameters.** The named argument `x_pos := …` overrides.
2. **Results.** `fn f(…) → Pos<A>` returns an `A` and declares
   `f::pos(…): 0 < f(…)` ([[function-owned-members]]), registered as an
   evidence rule. The body's positivity is an obligation, resumable when it
   is not discharged.
3. **Record fields.** `den: Pos<Nat>` is `den: Nat, den_pos: 0 < den`, with
   a rule `0 < r.den`.

A property not worth a name stays an ordinary proof parameter; there is no
general `where` form (Minus, 2026-10-10).

## What it assumes from elsewhere

- **[[infer-proposition-evidence]]** owns the search the sugar relies on.
- **[[function-owned-members]]** owns the `f::pos` name.

## Log

- 2026-10-10: Filed from [[positivity-evidence]].
