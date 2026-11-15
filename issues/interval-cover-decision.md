---
title: Decide finite covers of rational intervals, sound for the localic line
status: open
labels: [stdlib,mathematics,locale-theory,tactics,decision-procedure]
area: mathematics
created: 2026-11-10
updated: 2026-11-10
---

Whether finitely many rational intervals cover a rational interval is a
computation. Give it a Bool checker over `List<QInterval>` and prove it sound
for the line's cover: a list that holds every rational of `(lo, hi)`
(`RealLine::FinSub`'s second half) covers each interval strictly inside it,
`RealLine::Cov`. This is the converse of `RealLine::compact`
(lib/std/locale/real_locale.hthr), so a finite cover becomes a closed verdict
(`b = True` by `refl`, docs/proof-patterns.md) and Heine–Borel's output can
be fed back in.

## Scope

- The checker: sort or sweep the ends; a chain of overlapping members from
  below `lo` to above `hi`.
- Soundness by induction on the chain with `RealLine::glue`.
- A `by cover` surface only if a client wants one. The first client is
  [[closed-interval-compact-sublocale]], where "this finite family covers
  `[a, b]`" is the usual side condition.

Design: docs/library/localic-reals-design.md §7.
