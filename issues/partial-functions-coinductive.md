---
title: partial fn denotes a coinductive computation, so specifications carry no fuel
status: open
labels: [design,termination,coinduction,native]
area: language
created: 2026-10-31
updated: 2026-11-06
---

Item 5, part 2, of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): a function that may not terminate says `partial`
and denotes a coinductive computation, instead of taking a fuel argument that
its theorems then have to mention. Minus has said fuel should stay out of
statements (the itree rounds).

## Scope

- `partial fn` lowers into the coinductive tree library: a `Delay`, or an
  `ITree` with no events (`docs/coitree-design.md`). Its theorems are about
  convergence, through the coinductive↔fuelled bridge (`coitree_bridge.hthr`).
- `runtime fn` programs that loop until EOF or forever use it
  ([[runtime-fn-default-setup]]).
- Fuel stays where a budget is part of the meaning (a tactic's search
  depth). The sequencing design's `while … fuel` remains the explicit form.

## Done when

A function whose divergence is real is restated with no fuel in its
statements, its soundness proved by fixpoint induction (done: the kernel
model's `Tm::whnf_co`); a `partial fn` surface elaborates onto
`CoTree::iter`/`CoTree::rec` (after sequencing R2/R3); and a `partial`
runtime loop compiles under the default setup (after R5). The decimal
formatter is not a customer: its fuel is a termination witness, which
`unfolding-computed-scrutinee` and `while … decreases` own (Minus,
2026-10-31).

## Log

- 2026-10-31: Assessed in `docs/partial-functions-design.md`. The
  coinductive library already has everything except `CoTree::rec`. A probe
  builds it as a loop over the pending tree (`iter`, Coq's `interp_mrec`):
  its unfolding laws hold by `refl` at open arguments, runs at literals check
  by a count and `refl`, and the cost is linear in calls. The note proposes
  `partial fn f(x: A) → B` as `f : A → CoTree<B>(E)`, with tail recursion
  lowered to `iter`, and the general case to `rec`; proofs go through
  library rules (`Returns`, fixpoint induction, a measure rule,
  `Partial::get`). It also proposes changing "done when": the decimal
  formatter's fuel is a termination witness (its fix is
  `unfolding-computed-scrutinee` and `while … decreases`), so the customer
  should be the kernel model's `Tm::whnf`, whose divergence is real. Three
  rounds in §6, for Minus's decision.
- 2026-10-31: Minus agreed with the note and the change to "done when".
  Round 1 (the library) landed: `lib/std/itree/coitree_rec.hthr` has
  `CoTree::rec`/`mrec`, the unfolding laws, `Returns`, fixpoint induction
  (`Safe`, `safe_bind`, `rec_sound`), `mrec_bisim`, `mrec_bind`,
  termination by a measure (`Reaches`, `rec_total`) and `CoTree::get`.
  The customer is `lib/kernel_model/kernel_whnf.hthr`: `Tm::whnf_co`, with
  `whnf_co_sound` proved by `rec_sound` and no fuel anywhere. Probes in
  `lib/_tests/std/itree/coitree_rec_tests.hthr` and
  `lib/_tests/kernel_model/kernel_whnf_tests.hthr`. The bridge to
  `Program::rec` is [[coitree-rec-program-bridge]]. Left here: the surface
  (round 2) and runtime loops (round 3). Also not yet done: proving that
  `Ω` never returns, which needs a lemma saying a λ's only reduct is itself.
- 2026-11-03: Round 2 is now [[partial-fn-surface]], and round 3 (runtime loops) is
  [[effectful-loops-without-passes]], after Minus decided that loops over a
  world mean `Io → Partial<Mutated<Io, R>>` (`docs/effects-capabilities-design.md` §4).
- 2026-11-03: Round 2 built ([[partial-fn-surface]], closed): `partial fn` and `while` with no measure; docs/partial-functions-design.md §9. The tail case to `CoTree::iter` is [[partial-fn-tail-iter]], which round 3 (partial `runtime fn` loops) wants.
- 2026-11-04: Round 3's customer half done ([[effectful-loops-without-passes]], closed): `Io::tac`, `Io::sort`, `Io::cat` and `Io::write_all` are `while` loops with no measure, meaning `Io → Partial(Mutated<Io, R>)`, and a `Source`'s `Repeat` has a fuel-free denotation (`native_source_co`). Still left for partial `runtime fn` loops: the setup lowering them (R6) and [[partial-fn-tail-iter]].
- 2026-11-05: gardener: cites a file it shares with [[codata-up-to-friends-round-2]] (`docs/coitree-design.md`).
- 2026-11-06: [[partial-fn-tail-iter]] done: a tail-only `partial fn` is `CoTree::iter` of a pass, proved with `CoTree::iter_sound` (docs/partial-functions-design.md §10). Left for partial `runtime fn` loops: the setup lowering them (R6).
