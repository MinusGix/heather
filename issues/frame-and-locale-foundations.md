---
title: Develop frame and locale foundations
status: closed
labels: [stdlib,mathematics,locale-theory,order,research]
area: mathematics
created: 2026-09-02
updated: 2026-11-09
---

Build the point-free foundation needed before localic real numbers: complete
lattices/suplattices, frames with finite meets distributing over arbitrary
joins, frame homomorphisms, locales as the opposite category, and a practical
presentation basis suitable for predicative Heather.

The design must confront universe size and arbitrary-join representation
directly. Begin with finite/generated frames and formal-topology-style
presentations rather than assuming an impredicative powerset. Include points
as maps only as a derived notion; a locale is not defined by its points.

## What it assumes from elsewhere

- **[[lattice-structure-api]]** owns finitary lattice vocabulary.

## Log

- 2026-09-02: Filed as an independent locale-theory program and prerequisite
  for point-free reals.
- 2026-10-23: Pointers from Arend (`docs/surveys/arend-survey.md` §7). `arend-lib`'s
  `Locale` has `Join : (E → \Prop) → E`, which is small only because its
  `\Prop` is impredicative, so the definition does not port. Its construction
  route does: preorder sites, and `SiteLocale P` as the reflection of a site
  into locales, are how it builds the locale of reals and spectra of rings by
  generators and relations, which is this issue's formal-topology start.
  Schemes are locally ringed locales with affineness stated intrinsically
  (principal opens, localizations), a long-range customer. For reals, Isaev's
  cover spaces (arXiv:2412.20835) are a point-set alternative: completing `Q`
  by Cauchy filters gives the Dedekind reals, cover maps `R → R` match locale
  morphisms, and compactness reads "every Cauchy cover has a finite subcover".
- 2026-11-02: The finitary vocabulary this assumes now exists (`lib/std/algebra/lattice.hthr`, docs/library/lattice-structure-design.md): meets, joins, lattices and bounds over `PartialOrderRel(≈, ≤)`, relation-indexed, so a frame of opens can be ordered modulo a setoid with no extensionality. Distributivity is not a class yet; a frame would add it with its arbitrary joins.
- 2026-11-09: Landed (docs/library/frame-locale-design.md). `lib/std/locale/`:
  `frame.hthr` has the layered classes at `Type<1>` (`Preorder1`,
  `FiniteMeets`, `SupLattice`, `Frame`; joins over small families, equality
  as the mutual order), `FrameHom` with identity and composition,
  `LocaleMap` (a frame homomorphism backwards), `Omega` (the one-point
  locale), `Point` as a map from it with the completely-prime laws proved,
  and the spatial frames `Opens<X>` with points and preimage maps.
  `nucleus.hthr` has nuclei, the sublocale's frame on the same carrier at the
  order `x ≤ c(y)`, its inclusion, and `¬¬` on `Omega`.
  `formal_topology.hthr` has axiomatic formal topologies presenting frames,
  basic opens as a basis, and the Alexandrov topology. Elaborator: dot sugar,
  the `T::C(…)` spelling and the class telescope now handle a class carrier
  declared at a universe. Residue: [[inductive-formal-covers]] (covers from
  axioms, Heyting implication), [[record-universe-parameters]],
  [[implicit-type-argument-above-its-level]], and level polymorphism
  ([[implicit-level-polymorphism]]) to merge the `Type<1>` copies with
  `lattice`'s classes.
