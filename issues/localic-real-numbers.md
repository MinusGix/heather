---
title: Present the real line as a locale
status: open
labels: [stdlib,mathematics,reals,locale-theory,research]
area: mathematics
created: 2026-09-02
updated: 2026-11-10
---

Construct the localic real line from a rational-interval or formal-topology
presentation. Prove the frame/cover relations, arithmetic or order maps that
are natural point-free, and the relationship between points of the locale and
located real-number presentations under explicitly stated assumptions.

This is not another carrier implementation of `Real`. Spatiality and enough
points are conclusions or imported principles, never definitional premises.

## What it assumes from elsewhere

- **[[frame-and-locale-foundations]]** owns frames, locales, presentations,
  and universe policy.
- **[[inductive-formal-covers]]** owns covers generated from axioms, which a
  rational-interval presentation is.
- **[[real-presentation-comparison]]** owns comparisons with point-based
  presentations.

## Log

- 2026-09-02: Filed as a long-range customer; blocked until a usable
  predicative locale foundation exists.
- 2026-11-09: Foundations landed (docs/frame-locale-design.md); now waits on
  [[inductive-formal-covers]] for the interval axioms' cover.
- 2026-11-09: Unblocked: inductive-formal-covers is done; the real line is presented by an axiom set over rational intervals and `Cover` (lib/std/locale/formal_topology.hthr).
- 2026-11-10: The line is presented and its first theorems are in (docs/localic-reals-design.md): `lib/std/locale/presentation.hthr` (the universal property `Cover::hom`: a map out of a presented frame is checked on generators; `FormalPoint`), `real_locale.hthr` (`QInterval`, `RealAxiom` with `Shrink` and `Split`, the frame, Heine–Borel `RealLine::compact` by induction on the cover, `nontrivial`, `basic_reflects`, `RealLine::negation`), `real_point.hthr` (`CReal::formal_point`, covers sound for reals, `neg_point`). Stays open as the umbrella for what remains: [[localic-real-points-are-cauchy]] (the converse and round trip), [[locale-products-and-real-arithmetic]] (addition and multiplication as maps), [[closed-interval-compact-sublocale]], [[interval-cover-decision]]; the same tool at other spaces is [[presented-spaces-cantor-baire]]. Worked around: [[implicit-constant-family-record-parameter]], [[linarith-rat-without-ordered-field-import]].
