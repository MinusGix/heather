---
title: Register type code functions for tier-2 declarations (Tac as an η-short constructor)
status: open
labels: [elaboration,inductives,performance]
area: language
created: 2026-10-31
updated: 2026-11-06
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

## Log

- 2026-11-01: Binding statements ([[binding-statements]]) make this the cost
  of every `let x <- e;` over `Tac`: the lowering is `Bind::seq` at
  `M := λ A. ⌜Tac<El A>⌝`, and each `M(X)` in the call's types is a β-redex
  over Tac's whole code that the gate decodes and compares structurally
  against the inline `Tac<X>`. Measured on probes (`--timings`, one call):
  `Bind::seq(goal(), λ j => Pure(j.target))` costs ~19k conversion queries
  where `goal().bind(…)` costs ~3k; the same higher-order helper without the
  class costs the same 19k, and at `M := Option` (which has a code function)
  the two spellings cost the same. On the whole-tree A/B of mono's probes
  (`scripts/perf ab --whole-tree`, mono ported to binding statements) mono's
  own declarations roughly double their gate counters (`mono_with` 10.7k →
  100k steps) and the run's total seconds rise by a few percent. Landing the
  code function should return the ported modules to their old counts.
- 2026-11-05: gardener: cites a file it shares with [[parametric-type-families]] (`docs/higher-kinded-classes-design.md`).
- 2026-11-06: The same β-redex is why seven tactic metaprograms' meaning
  checks ([[recursion-meaning-check]]) run out of fuel (`mono_prove`,
  `mono_class_carrier`, `solutions`, `rt_go`, `Act::traced`,
  `norm_num_reify`, `interval_reify`). It is paid per **arm**: a `match` on
  a bound value inside `Bind::seq`'s continuation has the motive `M(B)`,
  and each of its arms is checked against it. Probe, an 11-constructor
  `Head` match under `let v <- view(h);` with no recursion: ~140k gate steps,
  against ~30k for the same code written `view(h).bind(λ v => …)`;
  ascribing the `match` `: Tac<Nat>` halves it. The meaning check gates the
  body a second time and compares the arms pairwise, so a recursive
  function with a few such matches crosses the default conversion budget
  (`mono_prove` holds at 16× the budget). Landing the code function should
  let those seven settle.
