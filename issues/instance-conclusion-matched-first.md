---
title: Match an instance's conclusion against the goal before building the candidate
status: open
labels: [traits,resolution,unification]
area: language
created: 2026-11-02
updated: 2026-11-02
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
