---
title: The closed interval as a compact sublocale; uniform continuity from continuity
status: open
labels: [stdlib,mathematics,reals,locale-theory,analysis]
area: mathematics
created: 2026-11-10
updated: 2026-11-10
---

`RealLine::compact` (lib/std/locale/real_locale.hthr) is Heine–Borel stated on
covers of a basic open. State it where it is used: `[a, b]` as a closed
sublocale of the line (a nucleus on the same carrier,
lib/std/locale/nucleus.hthr), and compactness as a statement about its frame
(a family whose join is the top has a finite subfamily whose join is).

## Scope

- The closed nucleus of an open (`c(u) = u ∨ complement`), at `[a, b]`.
- Compactness of that frame from `RealLine::compact`.
- The first consumer: a map out of `[a, b]` is uniformly continuous, as a
  theorem with the modulus computed, where `closed_interval.hthr` takes the
  modulus as a hypothesis today. Then the supremum of a continuous function
  on `[a, b]`, and how it relates to `supremum.hthr`'s located sets.
- Needs fine covers ([[localic-real-points-are-cauchy]] step 1) and benefits
  from [[interval-cover-decision]].

Design: docs/localic-reals-design.md §7.
