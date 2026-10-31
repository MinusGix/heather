---
title: Register type code functions for tier-2 declarations (Tac as an η-short constructor)
status: open
labels: [elaboration,inductives,performance]
area: language
created: 2026-10-31
updated: 2026-10-31
---

Tier-2 declarations (lowered on `W` with a leaf predicate, such as `Tac`)
and codata register no `D#tycode_fn` (`inductive.rs`: "Tier 2 names its
leaf predicate and nothing else"). Since the higher-kinded-classes round
(`docs/higher-kinded-classes-design.md` §3.1, §5 item 4), that has two
visible costs:

- a bare `Tac` at `Type → Type` is spelled `λ A. ⌜Tac<El A>⌝` rather than
  the η-short reference, so a class field `M(A)` at `M := Tac` carries a
  β-redex;
- the unifier's `?M(Nat) ≟ Tac<Nat>` recomputes `Tac`'s open lowering per
  call (`Elaborator::constructor_spelling`) to recover the arguments.

Registering the code function retires both. It also changes the emitted
spelling of every `Tac<…>` in the library, since `respell_ty` would start
naming them. Kernel terms move, so the round measures with `scripts/perf ab`
(counters first) and runs the exact image lane.

## Done when

`register_ty_code_fn` covers tier 2 (or says why a declaration declines),
`constructor_spelling` is left for codata only, and the suite and the perf
comparison are recorded here.
