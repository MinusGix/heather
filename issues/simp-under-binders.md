---
title: simp: an equation's instance under a binder is not rewritten
status: closed
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

The same gap hides the body of an `∃`: `Exists(λ x => P(x))` takes its
predicate as a value, so a law (an equation, or `P ↔ Q` since
`docs/simp-design.md` §12) whose instance is in `P(x)` sits under that λ
(`below_exists` in the same test module). There the crossing is
`iff_exists_congr` over the pointwise `↔`, which wants the statement walk
to read a value-parameterised former's predicate argument. A `∀` is
crossed: its body is a statement one binder down.

## Log

- 2026-11-11: Built (docs/simp-design.md §13). The proposal here assumed `funext` as `=`'s pointwise evidence; Heather has none, so a λ is crossed by its consumer's own evidence: an equation with no instance for the transport is walked as a step of `RelId` (`Relations::identity_step_or`), and `lib/std/data/list_pointwise.hthr` states `PreservesRelation(Pointwise(RelId), RelId, …)` for `map`, `filter`, `count`. `under_a_binder` closes. An `∃`'s body is read off the record's lowering and crossed by `iff_exists_congr` (`below_exists`). Left, each small: evidence for more consumers; `by simp()`'s defaults inside an `∃` (view-of-value-parameterised-record).
