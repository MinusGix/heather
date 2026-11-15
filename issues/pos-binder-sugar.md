---
title: Pos<A> binder sugar: a value plus an inferred positivity hypothesis
status: closed
labels: [frontend,syntax,elaboration,stdlib,ergonomics]
created: 2026-10-10
updated: 2026-10-13
---

`x: Pos<A>` in a binder elaborates as `x: A, x_pos: 0 < x := infer`, for any
`A` with `0` and `<` designated. Nothing is wrapped: callers pass a plain
`A` and positivity is found by [[infer-proposition-evidence]]. Design:
`docs/library/positivity-evidence-design.md` §6 B.

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
- 2026-10-13: 2026-10-13: LANDED, all three positions, as a parser desugaring (docs/library/positivity-evidence-design.md §11). Parameters: `x: Pos<A>` is `x: A, x_pos: 0 < x := infer`. Results: `fn f(…) → Pos<A>` returns an `A` and declares `evidence theorem f::pos` (values implicit, solver parameters premises), proved by `positivity` over the restated body or by hand with `on ?pos := …;` (the route for recursion). Fields: `den: Pos<A>` is `den: A, den_pos: 0 < den` searched at construction, plus the rule `R::den_positive`. Tests: crates/elab/tests/pos_binder_sugar.rs. Residue filed: [[pos-sugar-library-adoption]] (no lib signature changed this round) and [[pos-sugar-unsupported-positions]] (member results, parameterised records, constructor fields).
