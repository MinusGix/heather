---
title: Match an instance's conclusion against the goal before building the candidate
status: closed
labels: [traits,resolution,unification]
area: language
created: 2026-11-02
updated: 2026-11-03
---

Instance search builds every candidate by elaborating a reference to it at
the goal (`resolve.rs` `build_candidate` → `elab_check`) and only then asks
whether it is of the goal type (`checks_at`). That is how #387 surfaced
("built, but not of the goal type" for every candidate), it is the fan-out
[[resolution-candidate-fan-out]] measures, and it is part of why a failing
`mono` search costs gigabytes ([[mono-failure-under-upcast-cost]]).
Meanwhile rewrite (`rewrite.rs` `match_spine`, repeated binders by
conversion) and the host's `match_at` are further matchers with their own
policies (docs/elaborator-principles-survey.md §4).

## Proposal

Match a candidate's conclusion against the goal with the elaborator's
unifier (checked assignment, δ-lazy at head mismatch) before elaborating its
premises, and drop candidates whose conclusion does not match. Rewrite and
`host::match_at` become the same unifier at a different transparency. A
discrimination index over conclusions is the later optimisation, which
[[resolution-candidate-fan-out]] owns.

## Acceptance

- [[decide-at-defined-proposition]]'s `decide_bit<F.Canonical(…)>()` finds
  `And::Decide` through one δ step.
- The resolution trace says "conclusion does not match" for a candidate
  rejected before building.

After [[unifier-checked-assignment]] and [[unifier-lazy-delta]].

## Log

- 2026-11-03: Done (the instance half). `Elaborator::conclusion_clashes` reads a registered instance's type past its parameters, each a fresh slot as an application's implicits are, and runs the elaborator's unifier (checked assignment, δ-lazy) against the goal with a `unification::Clash` listener. The unifier's one negative answer: two canonical forms of different kinds (type formers, code formers, `Zero`/`Succ`, numerals, `inl`/`inr`) met along a path of injective formers; below an application's arguments, a projection or an eliminator nothing is decided, and a head the pattern could unfold is never a clash. A clashing candidate is dropped unbuilt with "rejected: conclusion does not match" (`conclusion_clashes` counter). The acceptance's `decide_bit<Canonical(…)>()` resolves since [[unifier-lazy-delta]]; probes in `lib/_tests/std/core/bool_tests.hthr` (`Spread`, `no_decision`). The host's `match_at` was already the unifier (`unify_root` then conversion); rewrite's `match_spine` is the matcher left, filed as [[rewrite-matcher-on-unifier]]. The discrimination index stays [[resolution-candidate-fan-out]]'s.
