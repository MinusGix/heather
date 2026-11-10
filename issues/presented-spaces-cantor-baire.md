---
title: Present Cantor and Baire space as locales; the fan theorem as an induction on covers
status: open
labels: [stdlib,mathematics,locale-theory,codata,research]
area: mathematics
created: 2026-11-10
updated: 2026-11-10
---

The tool that presents the real line (`Cover`, `Cover::hom`, `FormalPoint`,
lib/std/locale/presentation.hthr) presents other spaces with one axiom each.
Cantor space: basis finite lists of bits ordered by extension, axiom "a
prefix is covered by its two one-bit extensions". Baire space: the same over
`Nat`, an infinitary axiom, which `Cover`'s function-valued premise already
allows.

## Why

- For the locale, compactness of Cantor space (every cover of a prefix has a
  finite subcover, a bar is uniform) is an induction on the cover, as
  `RealLine::compact` is. It is the fan theorem, proved, not assumed.
- Points are streams. A continuous function on streams given on generators is
  then uniformly continuous as a program: a modulus read off the cover. This
  bears on `CoTree`, interaction trees and anything that consumes input
  lazily (docs/localic-reals-design.md §7).
- Binary expansions map Cantor space onto `[0, 1]`: a second proof of the
  interval's compactness and a test of maps between presented locales.

## Scope

- The two presentations, compactness of Cantor space, points from
  `Nat → Bool`, and one uniform-continuity statement with its modulus
  computed in a probe.
