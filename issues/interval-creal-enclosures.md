---
title: Interval enclosures of Cauchy reals and decided CReal comparisons
status: open
labels: [reals,intervals]
area: mathematics
created: 2026-10-26
updated: 2026-10-26
---

Intervals are stated at `Rat` (`Interval::Has`, `lib/std/num/float/interval.hthr`).
The issue that built them names "deciding `CReal` comparisons at concrete
arguments by evaluation" as a customer. A regular `CReal` `x` has
`|x - x.seq(n)| <= 1/(n+1)`, so `[x.seq(n) - 1/(n+1), x.seq(n) + 1/(n+1)]`,
each bound rounded outward to dyadics, encloses `x`; two enclosures that
separate decide `x < y`.

Scope:

- containment at `CReal`, `ofRat(lo) <= x <= ofRat(hi)`, for the constant
  enclosure of a `Rat` and for `+`, `-`, `*` (the latter needs the order
  lemmas for `CReal` products);
- `CReal::enclose(x, n, p)` from the sequence, with its containment
  theorem;
- `x < y` from `enclose(x, n, p).below(enclose(y, n, p)) = True`, with a
  refinement over `n` as `IntervalExpr::lt_search` refines over `p`.

`creal.hthr` was being worked on by the Cauchy reals completeness round
when the intervals landed, so this round was kept out of it.

## What it assumes from elsewhere
- **[[dyadic-interval-enclosures]]** (closed) owns `Interval`. Assumed
  here: only `Interval::Has` at `Rat` and the operations' containment
  theorems.
- **[[regular-cauchy-reals]]** owns `CReal`. Assumed here: only the
  regularity bound and `CReal::ofRat`'s order embedding.
