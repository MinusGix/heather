---
title: A lemma proved at a class-constrained carrier elaborates two orders of magnitude slower than its concrete twin
status: open
labels: [elaboration,performance,traits]
area: language
created: 2026-10-30
updated: 2026-10-30
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
