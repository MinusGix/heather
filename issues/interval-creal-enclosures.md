---
title: Interval enclosures of Cauchy reals and decided CReal comparisons
status: closed
labels: [reals,intervals]
area: mathematics
created: 2026-10-26
updated: 2026-10-27
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

## Log

- 2026-10-27: LANDED: `lib/std/num/float/creal_interval.hthr` (design
  `docs/floating-point-design.md` §16, "Enclosures of reals").
  `Interval::HasReal` is containment at `CReal` through `CReal::ofRat`;
  constants, `neg`, `add`, `sub`, `mul` (corner search and the direct
  positive path) and `pow` keep it. The product's sign split on a real
  factor happens inside the `≤`'s refutation (`CReal::le_by_sign`), so no
  sign is decided. `CReal::enclose(x, n, p)` rounds the term's
  `±1/(n+1)` outward, with `enclose_has`; `CReal::lt_of_enclose` /
  `le_of_enclose` decide from one pair of enclosures, and `RealExpr`
  (`RRat` exact leaves, `RReal` leaves from their terms) refines the index
  on a miss in `lt_search`. `by intervals()` reads goals at `CReal::Lt` /
  `CReal::Le` too. Order facts added to `creal.hthr`: `neg_le`, `neg_lt`,
  `mul_le_mono_r_nonpos`, `le_by_sign`, `le_term_add`, `term_sub_le`. The
  ordered-field statement still waits on `float-reals`. Residue:
  reciprocals are [[interval-creal-reciprocal]].
