---
title: Prove inequalities over variable boxes by interval bisection
status: open
labels: [mathematics,tactics,reals]
area: mathematics
created: 2026-10-28
updated: 2026-10-28
---

`by intervals()` proves closed comparisons by evaluating enclosures, and
refuses a leaf that does not compute, such as a variable
(`lib/std/tactic/interval_tactic.hthr`, docs/floating-point-design.md §16).
CoqInterval and Flyspeck prove inequalities with free variables by
confining each variable to a box and bisecting it.

Sketch (docs/nonlinear-arithmetic-design.md §8):

- Facts `lo <= x`, `x <= hi` with closed bounds make `x` an interval leaf.
  This requires containment with a variable leaf in `IntervalExpr`/`RealExpr`,
  where the leaf's box is the hypothesis.
- On a miss, split the variable whose interval is widest, up to a box budget.
- The certificate is a tree of `lt_of_search`/`le_of_search` verdicts joined by
  a cover lemma (`lo <= x <= m` or `m <= x <= hi`). At `CReal` the split
  point must be a strict overlap (`x < m + ε` or `m < x`), by cotransitivity,
  because `x <= m ∨ m <= x` does not hold there.

It proves strict goals on bounded boxes, including polynomial bounds that
`nlinarith`'s heuristic does not find (`x³ − x + 1 > 0` on `[-1, 1]`), and
later transcendental ones. It cannot prove tight goals (`0 <= x·x` at
`x = 0`) or use unbounded variables. Those belong to `nlinarith`, so the two
are complementary. The cost is exponential in the number of variables
bisected.

No customer yet. Candidates are the float error bounds and the analysis
layers' sign facts (docs/analysis-foundations-design.md §3.5, where Gruntz's
sign facts come from `by intervals()`).

## What it assumes from elsewhere

- **[[dyadic-interval-enclosures]]** (closed) owns the enclosures and the
  verdict lemmas. Assumed here: `lt_of_search`/`le_of_search` and their
  vacuous reading of crossed bounds.
