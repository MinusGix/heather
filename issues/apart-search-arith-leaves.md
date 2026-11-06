---
title: Let arithmetic reach the leaves of the sign rules
status: closed
labels: [proofs,solver,arithmetic,mathematics]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-06
---

A divisor's apartness (docs/division-design.md §2) is searched through the
sign rules (`Positive`/`Negative`/`NonNeg` through `+`, `*`, `/`, `⁻¹`,
powers, `abs`), and `nlinarith` runs only as a search rule about
`Apart`, on the whole divisor. So a divisor whose sign needs arithmetic at
a *leaf* is refused:

```heather
fn f(a, b, c, e: Rat, h: b < c) → Rat { a / ((c - b) + e.abs()) }   // refused
```

`(c - b)` is positive by `nlinarith` and `e.abs()` nonnegative by a rule,
but no route combines them: the top-level `nlinarith` reads `abs(e)` as an
atom with no fact, and `positive_add_nonneg`'s premise `(c - b).Positive()`
runs no arithmetic. Probe: `div_arith_leaf` in
`lib/_tests/std/num/rat_tests.hthr` (an `expect-error`).

A second, smaller gap: a positive local is never read as `NonNeg` (a rule
`Positive ⇒ NonNeg` fails Paterson's condition, its premise being no
smaller), so `x * y` at `0 < x`, `0 <= y` is not `NonNeg`.

Why the fallback is not at `Positive` today: `apart_of_negative` is tried
before `apart_of_positive`, so every `x⁻¹` at a positive local would first
pay a failing `nlinarith` at `x.Negative()`. Ways out:

- a search phase for search rules *across relations*: run every plain rule
  of the whole search tree first, then search rules at the leaves that are
  left (positivity's omega-at-leaves, docs/positivity-evidence-design.md
  §10, is that shape for one tactic);
- order candidates by the goal: try the side a local fact names first;
- `nlinarith` hints from the sign rules: hand the top-level call the
  `NonNeg` facts the rules can prove about its atoms (`0 <= e.abs()`).

The third is the cheapest and would also cover the `NonNeg` gap.

## Log

- 2026-11-06: Done (docs/division-design.md §2–3): search rules `positive_add_by_nlinarith`, `positive_sub_by_nlinarith` and the negative pair, keyed by `+`/`-` so a local never runs them, and `nonneg_by_linarith`, which reads a positive local as nonnegative. `div_arith_leaf` is now a passing probe. Search rules are skipped inside an arithmetic tactic's own run, which this needed: nested `nlinarith` runs blew `rat_den_sum` past its rail.
