---
title: Prove interval containment once, over an ordered field, and read it at Rat and CReal
status: open
labels: [reals,intervals,refactor]
area: mathematics
created: 2026-10-30
updated: 2026-10-30
---

`lib/std/num/float/creal_interval.hthr` proves 26 `Interval::*_real`
theorems that restate `interval.hthr`'s containment lemmas at `CReal`, with
`CReal`'s order lemmas in place of `Rat`'s (`neg_has_real`,
`add_bnd_has_real`, `between_l_real`, `corner_lo_real`, `mul_box_has_real`,
`recip_pos_has_real`, `lt_of_below_real`, …). The arguments are the same
corner arguments; the file's own header says so. Every proof-shape cleanup
(the 2026-10-30 round's `bnd_has_of`/`widen_has`) has to be done twice, and
the `CReal` copy was not.

The direction: state `Has` against an `OrderedField(≈, <, <=, +, *)`
dictionary and an embedding of the bounds (`Dyadic → Rat → K`), prove each
operation's containment once inside a `section<K: OrderedField(…)>`, and
make `Interval::Has` and `Interval::HasReal` the readings at `Rat` and at
`CReal`.

What has to be settled first:

- **The product's sign split.** `interval.hthr` splits on `Rat::le_total`;
  at `CReal` the sign is never decided, and `between_r` goes through
  `CReal::le_by_sign` inside the refutation a `≤` is. The generic proof
  takes the refutation route (a `PseudoOrder`'s `≤` is the negated `<`), so
  `Rat` would pay a refutation where it now pays a decision. Whether that
  costs anything measurable at the checker's `refl` is the first
  measurement; the containment theorems are not evaluated, so likely not.
- **The embedding.** Bounds are `Dyadic`; `K` needs `Rat → K` (the
  float design's transfer lemma) with `+`, `*`, `-`, `≤` preserved, i.e. an
  ordered-field homomorphism from `Rat`, of which `CReal::ofRat` is one and
  the identity the other.
- **Reciprocals** differ in kind (`x.recip()` total at `Rat`, an `Apart`
  proof at `CReal`), so `recip_has` probably stays per carrier.
- **Class-law cost.** [[mono-class-laws]]'s note on class carriers applies:
  a class law at a concrete carrier carries an upcast per use.

Payoff: about half of `creal_interval.hthr` becomes instantiations, and the
next carrier gets
containment for free.
