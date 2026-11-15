---
title: A lemma proved at a class-constrained carrier elaborates two orders of magnitude slower than its concrete twin
status: closed
labels: [elaboration,performance,traits]
area: language
created: 2026-10-30
updated: 2026-10-31
---

Found by the assessment of [[interval-containment-once-over-ordered-field]]
(2026-10-30). The same proof written once inside
`section<K: OrderedField(≈, <, <=, +, *)>` (or a child class) and once at
`CReal` or `Rat` costs seconds in the first case and milliseconds in the
second. The kernel gate is small in both; the difference is the
elaborator's. `ordered_field.hthr`'s own lemmas pay the same
(`OrderedField::mul_le_mono_l`, `recip_lt_recip`: about a second each,
against tens of milliseconds for a `Rat` lemma of the same size), so this is
how generic proofs cost today, not something one file does.

Measured with `--only` (one box, counts are the datum):

- `Interval::between_l_in` (generic, prototype) against
  `Interval::between_l_real` (the same corner argument at `CReal`): body
  elaboration ~500× the time; `decls_gated` 3,198 against 31;
  `local_subst_nodes` ~4M against ~22K; `check_terms` 227 against 9;
  `projection_subst` the largest named elaborator column; eval steps 8.8K
  against 331.
- A section one class deeper costs more again: the same lemma
  (`mul_le_mono_l_nonpos`) in `section<K: OrderedFieldOfRat(…)>` against
  `section<K: OrderedField(…)>` is about 1.6×, so the cost grows with the
  depth of the hierarchy a field read goes through (`K.rel_sym` is a read
  through `OrderedField → LocatedAddGroup → OrderedAddGroup/PseudoOrder →
  StrictOrder → Equivalence`).

What to find out: where `decls_gated` and the substitution volume come
from at an open carrier (per field read? per explicit point? per `let`
whose type mentions the dictionary?), and whether the named per-instantiation
projections ([[per-instantiation-projection-boundaries]]) or the closed
[[upcast-assembly-cost-at-open-carriers]] read-through already cover part
of it. The prototype is the reproducer (the project's shared files,
`interval-once/interval_generic_proto.hthr`; move it under `lib/_tests` to
run it).

Why it matters: every "prove it once over the class" refactor (intervals,
`linarith`'s certificates, `mono`'s class laws, the analysis layers) trades
duplicated text for this cost in the cold gate.

## Log

- 2026-10-31: The plain generic lemmas are much cheaper on today's master
  (the interval section's lemmas written with named laws elaborate in
  well under a second each, `mul_box_has_in` included). Tactics are the
  outlier now. `by mono_with` at a class carrier, reading images through a
  morphism parameter ([[cast-reading-through-local-morphism]]), costs tens
  of seconds per lemma and millions of kernel steps. Its `CReal` twin,
  reading through a registered edge, costs milliseconds. Measured on the
  interval round's section: `between_l_in` (four calls) and `neg_has_in`,
  `add_bnd_has_in`, `mul_pos_has_in` (two each) each spent 20–60 s and
  2–5M steps. The same four lemmas with `hom.map_*` laws and
  `StrictOrder::le_of_same_l/_r` each take under a second. So
  `interval.hthr`'s generic section names the laws. Make `mono` cheap at a
  class carrier and those proofs can go back to two lines each.
- 2026-10-31: Root causes found and fixed; closed.
  - **Plain generic lemmas: the dictionary field walk.** A field read off a
    class dictionary at an open carrier takes `project_field`'s structural
    walk (`emits_at_forms`; the per-instantiation projection names do not
    cover class dictionaries, [[per-instantiation-projection-boundaries]]).
    The walk substituted each earlier field's projection into the whole
    remaining spine at every step, so a read cost the field's depth times
    the dictionary type's size, and a deep class's dictionary type is large
    (`K.rel_sym` sits under every ancestor's laws). That was
    `projection_subst`, the largest named column above. The walk now
    descends a spine that is a `Σ` outright without substituting and
    substitutes the earlier projections once, into the field's type alone
    (a tail that is not a `Σ` outright is substituted then and exposed by
    `whnf`, as before). Same terms, one box, cold check of the closure
    under `lib/std/num/float/interval.hthr`: `ordered_field` 24.0 s →
    3.3 s, `linarith` 10.9 s → 1.5 s, `ring` 5.9 s → 2.2 s, `interval`
    5.2 s → 1.5 s; `projection_subst` 17.3 s → 0.06 s in `ordered_field`.
    `OrderedField::mul_le_mono_l` 1.4 s → 0.15 s, `recip_lt_recip`
    1.2 s → 0.15 s: the same order as a `Rat` lemma of that size.
  - **`mono` at a class carrier: the host's re-reads.** Building a law's
    application one hole at a time (`cast_holes`, `cast_slots`,
    `apply_slots`) asked for each prefix's type, and the host re-reified
    every prefix from scratch: quadratic in the spine (nineteen leading
    parameters for a morphism law) over a large record type. On top, `mono`
    re-read the morphism edges in scope (a law check per morphism local) at
    every leaf's push, order and fact probe. Now the host remembers the
    applications it reified (`Run::readings`), a new `Holes(e, n)` request
    makes a spine of holes in one step, and `mono` reads the edges once per
    run (docs/metaprogramming/host-elaboration-interface-design.md §20). `by mono_with`
    reading `map(Dyadic::add(a, c).rat()) <= x + y` through the section's
    morphism: 4.3 s → 0.9 s per lemma; its `CReal` twin through a
    registered edge is ~0.5 s, so the class carrier is now within 2× of a
    concrete one.
  - **The interval proofs stay with the named laws.** Measured with the
    two-line `mono_with` proofs restored in the generic section:
    `neg_has_in` 0.9 s, `add_bnd_has_in` 0.8 s, `between_l_in` 1.6 s,
    against 50–100 ms each for the named-law proofs after the walk fix. A
    `mono` call costs ~0.3 s of tactic evaluation and `apply` matching at
    any carrier, which is `mono`'s own price, not the class carrier's.
