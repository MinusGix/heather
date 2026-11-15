---
title: Instance search does not unfold a defined proposition to its connective
status: closed
labels: [traits,decidability,elaboration,ergonomics]
area: tactics
created: 2026-10-30
updated: 2026-11-03
---

`decide_bit<F.Canonical(mag, bexp)>()`, with
`fn Format::Canonical(…) → Type { A ∧ B ∧ (C ∨ D) ∧ (E → G → H) }`, finds no
instance: every connective candidate (`And::Decide`, …) is refused with "the
goal of `#constraint0` (`Decide<P>`) still mentions an implicit that could not
be inferred". Unifying the instance head `?P ∧ ?Q` against the goal does not
δ-unfold `Canonical`, so the type parameters stay unsolved. (A *value*
parameter does get there by unfolding: `Le(?n, ?m)` against
`unsigned_lt(64, …)`, docs/tactics/reflection-through-decide-instances-design.md §2.)

Workaround in use: spell the proposition at the `decide_bit` site
(`Format::canonical`, issues/decide-bit-is-the-comparison.md), and let
`decide_intro` / `decide_elim` infer it.

Fix candidates: (a) after every candidate fails at a goal whose carrier head
is a transparent `fn` into `Type`, retry once at the carrier's one-step δ
unfolding (only on the failure path, so no hot-path cost); (b) a derived
instance at the definition (`derive Decide` on a proposition,
[[derive-decide-instances]]). (a) also makes named propositions
(`Canonical`, `Spec`s) decidable without a declaration each.

Related: [[decide-bit-is-the-comparison]], [[omega-unfolds-defined-propositions]].

## Log

- 2026-11-03: Resolved by [[unifier-lazy-delta]]: the unifier unfolds the goal's carrier (`Canon(a, b)`) to its next head where the instance head `?P ∧ ?Q` does not meet it, so `And::Decide` is found with no retry. Probes `spread_bit`, `spread_literal`, `spread_intro` in `lib/_tests/std/core/bool_tests.hthr` ([[instance-conclusion-matched-first]]).
