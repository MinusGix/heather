---
title: simp: an equation's instance under a binder is not rewritten
status: open
labels: [tactics,proofs]
area: tactics
milestone: [tac-general]
created: 2026-11-11
updated: 2026-11-11
---

An equation step is a `J` over the goal with the instance abstracted, so the
instance has to be closed in the goal's context. An instance that mentions
a bound variable is skipped by the finder, and `simp_only` reports no law
fired:

    theorem under_a_binder<A>(xs: List<A>, f: A → List<A>):
        xs.map(λ x => (f(x) ++ Nil).len()) = xs.map(λ x => f(x).len()) {
        simp_only(List::append_nil)
    }

(`lib/_tests/std/tactic/simp_tests.hthr`, `under_a_binder`). The relation
walk does cross a λ, by the pointwise relation (`docs/equation-rewrite-design.md`
§10.1), and `=` is a relation with `funext` as its pointwise evidence.

Wanted: an equation law whose instance sits under a λ fires through the
relation walk at `=` (pointwise `=` to `=` of the λs by `funext`, then the
enclosing context by congruence), and the failure report says "an instance
sits under a binder" when it does not.

Done when `under_a_binder` closes by `simp_only(List::append_nil)`.
