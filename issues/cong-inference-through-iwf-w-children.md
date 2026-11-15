---
title: Inferred cong does not see through the IWf-on-W route's rebuilt children
status: closed
labels: [elaborator,indexed-families,ergonomics]
area: language
milestone: [math-metatheory]
created: 2026-10-25
updated: 2026-10-25
---

On the `IWf`-on-`W` route (`docs/kernel/iwf-infinitary-design.md`), a value is a
pair `⟨tree, proof⟩`, and a `match` arm's child alias is rebuilt from the
pieces of its scrutinee (`⟨f'(⟨⟩), cs⟩`, `λy.⟨k y, cs y⟩`). When a function
is applied to a constructor built from another function's result, the
reduct mentions `⟨fst X, snd X⟩` and annotations spelled over the arm's
variables where the other side of a goal has `X`. The two are convertible
(Σ-η is in the kernel's conversion), but anti-unification is syntactic, so
an inferred `cong(p)` in such an arm fails with "cannot generalize … differ
under it at `pair@` against `variable`".

Reproduction (`crates/elab/tests/iwf_infinitary.rs`, `CP`): in
`cp_size`'s `One(m, s)` arm, `cong(cp_size(m, s))` is refused; the
explicit `succ_eq(size(m, cp(m, s)), size(m, s), cp_size(m, s))`, which
states the endpoints and leaves the rest to conversion, is accepted.

Options:

1. Compare up to Σ-η (and the annotation differences that come with it) in
   `lgg.rs`, contracting `⟨fst X, snd X⟩` to `X` on both sides first.
2. Spell the arm's goal and aliases so that the reduct is already
   contracted. This looks impossible in general: the pair is rebuilt by the
   *other* function's constructor, not by this arm.

Option 1 is the likely fix. It needs care that the generalized motive is
still checked by the kernel against the goal by conversion (it is, today).
The port's metatheory proofs will hit this in every congruence step under
a constructor of a logical relation.

## Log

- 2026-10-25: Filed from the IWf-on-W round
  ([[indexed-infinitary-families]]).
- 2026-10-25: Done, generally rather than by Σ-η contraction (option 1 alone did not
  suffice: the annotations differ too): `cong` gets a third attempt that
  anti-unifies the whnf'd sides with the hole allowed at any outermost pair
  of subterms converting to the endpoints, checked in `Γ, z` and then by the
  kernel at `?f`'s type (`lgg_body_up_to_conversion`, design §13).
  `cp_size` in `iwf_infinitary.rs` now uses plain `cong` in its one-child
  arms. The `k̄` arms still state endpoints for cost:
  [[elab-whnf-family-transport-cost]]. `rewrite` still finds occurrences by
  head, which a rebuilt child's reduct lacks (the `Two` arm keeps `add_eq`).
