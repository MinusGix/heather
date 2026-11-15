---
title: Separate Cauchy, conditional, and order completeness
status: open
labels: [stdlib,mathematics,reals,analysis,design]
area: mathematics
milestone: [math-reals]
created: 2026-09-02
updated: 2026-11-06
---

Design completeness capabilities only after writing their quantified data
precisely. Compare regular/Cauchy completeness with explicit moduli,
sequential completeness, least-upper-bound or conditional completeness, and
located/order completeness. Record exactly where countable choice,
extensionality, or classical principles relate them.

These should be orthogonal capabilities over ordered-field-like structures,
not one oversized `CompleteReal` class. Each proposed class needs a theorem
that consumes it and one presentation expected not to inhabit it
constructively.

## What it assumes from elsewhere

- **[[constructive-ordered-field-interface]]** owns the common scalar laws.
- **[[axiom-provenance]]** owns tracking imported principles.

## Log

- 2026-09-02: Filed to keep the Cauchy/Dedekind split visible in interfaces.
- 2026-10-26: `CReal` now inhabits regular-sequence completeness with the rate fixed at 1/(n+1) (`CReal::complete`, docs/library/creal.md), with uniqueness and the rationals dense as limits. A Cauchy-completeness capability can take its statement from there; `Rat` is the carrier expected not to inhabit it.
- 2026-11-06: 2026-11-06: Sequences round (docs/library/sequences-and-completeness.md). `Converges`/`CauchySeq` over any ordered field, with moduli as data, and the algebra, order and continuity of limits (lib/std/analysis/sequence.hthr). Cauchy completeness is the capability class `CauchyComplete`. Its consumer is the contraction mapping theorem (`Contraction::fixed_point`, `fixed_unique`). `CReal` inhabits it by reading a Cauchy sequence at its modulus and taking `CReal::lim` (real_complete.hthr). `Rat` is refused for lack of an instance; the ¬ theorem is [[rat-not-cauchy-complete]]. The table of notions, and where countable choice and LPO enter, is in the note's §2. Order completeness at located sets is next: [[order-completeness-located-sup]].
