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

The direction (decided 2026-10-30, see the log): state `Has` against an
`OrderedField(≈, <, <=, +, *)` dictionary and an ordered-ring morphism from
the bounds' type into it, passed as data (`φ: OrderedRingHom<Rat, K>`, the
morphism record [[casting-standard]] registers as a cast edge; identity at
`Rat`, `CReal::ofRat_hom` at `CReal`), prove each operation's containment
once inside a `section<K: OrderedField(…)>(φ: …)`, and make `Interval::Has`
and `Interval::HasReal` the readings at `Rat` and at `CReal`. No combined
class (`OrderedFieldOfRat`): the embedding is a morphism between two
structures, not a capability of one.

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

## Log

- 2026-10-30: ASSESSED, by a prototype (not committed: a scratch probe
  module importing `interval` and `creal_interval`). Feasible, and the four
  questions above are settled:
  - **Embedding.** A class beside `OrderedFieldOfInt`:
    `OrderedFieldOfRat<K>(≈, <, <=, +, *) extends OrderedField` with
    `of_rat: Rat → K` and its laws (`of_rat_le`, `of_rat_lt`,
    `of_rat_respects`, `of_rat_zero`, `of_rat_neg`, `of_rat_add`,
    `of_rat_mul`). `Rat`'s instance is the identity (every law is the
    hypothesis or `same_refl`), `CReal`'s is `CReal::ofRat` and the
    existing `ofRat_*` lemmas, unchanged. It has to live in `rat.hthr`
    (`ordered_field` is below `rat`), `CReal`'s instance in `creal.hthr`.
    A field, not `num · den⁻¹` derived from `of_int`: only a field makes
    the `Rat` reading the identity by conversion. The same class is what
    [[push-cast-through-embeddings]] would register for `CReal::ofRat`, so
    the two should agree on one spelling of an embedding.
  - **Readings.** `fn Interval::HasIn(self I, x: K)` inside the section
    converts to `Interval::Has` at `Rat` and to `Interval::HasReal` at
    `CReal` in both directions, at a neutral `I` too (the stuck matches
    compare branchwise and the dictionary's fields unfold to the carrier's
    globals). A generic `add_bnd_has_in` and `mul_box_has_in` were applied
    directly as `Has` and `HasReal` theorems; each reading checks in a few
    thousand kernel steps. So `Has`/`HasReal` keep their own definitions
    (diagnostics keep reading them) and the per-carrier names become
    one-line readings that `IntervalExpr`, `RealExpr` and `by intervals()`
    keep citing.
  - **Sign split.** `StrictOrder::le_by_cases(u, v, y, z, below: y < z →
    u <= v, above: z <= y → u <= v): u <= v`, proved in `≤`'s refutation
    with no decision and no cotransitivity, generalises
    `CReal::le_by_sign`; the generic `mul_box_has_in` uses it and its
    `Rat` reading checks. Its cost to `Rat` is nil where it matters: the
    containment theorems are never reduced (the checker's `refl` evaluates
    the search's `Bool`, not the soundness proof). A dyadic factor's sign
    (`between_l`) stays decided, by `Rat::le_total` on its image.
  - **What stays per carrier.** The reciprocals (`x.recip()` total at
    `Rat`, `x.inv(h := …)` at `CReal`), `of_rat_has`, the enclosures from
    terms and `apart_of_excludes`. Powers need either a `pow` field with
    `npow_zero/succ/add` laws on the class or stay per carrier:
    `Rat::npow` and `CReal::npow` are distinct fixpoints, so a generic
    `npow` would not convert to either at a neutral exponent.
  Of the 26 restated lemmas, about 17 fold into the generic section as
  they stand (respects, neg, add, sub, the corners, box, positive box,
  `mul_bnd`, `mul`, both verdicts, `has_of_has`), 5 more with a `pow`
  field, and the 7 `Dyadic::real_*` image laws become two generic ones.
  - **Costs.** Generic lemmas elaborate about two orders of magnitude
    slower than their concrete twins (seconds, not milliseconds; kernel
    gate small in both), the same as `ordered_field.hthr`'s own lemmas;
    a section one class deeper (`OrderedFieldOfRat` over `OrderedField`)
    costs more again, so laws that need only `OrderedField` belong in an
    `OrderedField` section. Net: the cold `std/num/float` gate gets slower
    by the generic layer's elaboration (tens of seconds), the warm path
    replays images and pays nothing; measure the folder against the rail
    in the round that lands it.
  - **Writing gotchas.** Inside the section `+`, `*`, `<=` bind to `K`'s,
    so dyadic and rational arithmetic in statements must be spelled
    `Dyadic::add(a, c)`, `Rat::mul(p, q)`, `Rat::Le(p, q)`; a section member
    named like a class field (`Interval::of_rat_add` beside `of_rat_add`)
    is refused as ambiguous; and the generic laws take explicit points, so
    a proof reads wordier than its `Rat` twin (`StrictOrder::le_respects`
    with six arguments where `Rat::le_of_same_of_le` takes two). Generic
    one-sided `le_of_same_of_le`/`le_of_le_of_same` would recover most of
    that.
  Sequencing: the convoys of [[elab-match-refines-hypothesis-kernel-rejects]]
  would otherwise be written once more in the generic section, so that
  issue first if it lands soon; the class's shape should agree with the
  casting decision in [[push-cast-through-embeddings]]. Independent small
  wins either way: `StrictOrder::le_by_cases` and
  `OrderedField::mul_le_mono_l_nonpos`/`_r_nonpos` (missing from the class
  layer today) belong in `ordered_field.hthr`.
- 2026-10-30: DECIDED with Minus: the embedding is a morphism record
  passed as a parameter, not the `OrderedFieldOfRat` class the assessment
  prototyped (combined X-of-Y classes exist only because two constraints
  installing the same `≈`, `+`, `*` are refused,
  [[constraints-sharing-indices]]). The record is
  [[casting-standard]]'s `OrderedRingHom` (docs/casting-design.md §5.6),
  so one value serves the cast graph and this section; take its field
  names. The readings still convert: at the identity morphism `HasIn`
  reduces to `Has` by β. Longer term the ℚ-embedding is derivable in every
  ordered field (`of_nat`, `recip`), with carriers proving only that their
  own spelling coincides with it; that would also retire `CommRingOfInt`
  and `OrderedFieldOfInt`. The containment proofs use only a monotone map
  commuting with `+`, `*`, `-` up to `≈`, so a `Dyadic → K` morphism (the
  composite through `Rat`) would let statements drop `.rat()`.
- 2026-10-31: RE-CHECKED on master after #290 (match refines hypotheses:
  the convoys are gone) and #286 (morphism records; `mono` reads images
  through cast edges, so most per-carrier proofs are now two `by
  mono_with` lines). The decided shape works: a
  `section<K: OrderedField(≈, <, <=, +, *)>({map: Rat → K}, hom:
  OrderedRingHom<Rat, K>(map, …, ≈, <, <=, +, *, K.inv, K.unit,
  K.multiplicative.unit))` header is accepted; a generic `add_bnd_has_in`
  read at `CReal` with `CReal::ofRat_hom()` and at `Rat` with an identity
  morphism, both by conversion. The identity needs a named map
  (`fn Rat::id(self q: Rat) → Rat { q }`): with `λ q => q` as the map the
  kernel refuses the reading with NotConvertible between two
  `OrderedRingHom<…>` types that display the same. Members of the section
  take `hom` explicitly, including sibling calls inside it
  (`Bnd(a, b).HasIn(hom, x)`, `Interval::image_add(hom, a, c, x)`). The
  blocker for doing it now is [[cast-reading-through-local-morphism]]:
  inside the section `mono` cannot read `map(Dyadic::add(a, c).rat())`
  through `hom`, so the generic proofs would be the long named-law form
  while the per-carrier ones are short. Since #286 the duplication is cheap
  (two short proofs instead of two long ones), so do that issue first, then
  this round becomes moving `creal_interval.hthr`'s proofs into the section.

