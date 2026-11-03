---
title: partial fn surface, and while with no measure in carriers that iterate
status: closed
labels: [design,termination,coinduction,sequencing]
area: language
milestone: [lang-sequencing,nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

Round 2 of [[partial-functions-coinductive]] (`docs/partial-functions-design.md`
§4.1–4.3, §6): the `partial fn` surface. Effectful loops need it first
(`docs/effects-capabilities-design.md` §4, decided by Minus 2026-11-03):
a loop over a world with no measure means `Io → Partial<Mutated<Io, R>>`.

## Scope

- `Partial<B>` as a library alias for `CoTree<B>(Events::none())` (Capretta's
  delay monad), with `Bind`/`Pointed` instances so it is a sequencing
  carrier.
- `partial fn f(x: A) → B` declares `f : A → Partial<B>` (or
  `CoTree<B>(E)` when it has events). Tail self-calls lower to
  `CoTree::iter` of a pass over the arguments; the general case to
  `CoTree::rec` (design §4.2). Refusals with reasons as §4.2 lists.
- **`while` with no measure in a carrier that can iterate.** A class for the
  iteration operator (`iter: (A → M(Step<A, B>)) → A → M(B)`, an Elgot
  monad: `Partial`, `CoTree<_>(E)`, and state over either) lets a carrier
  scope write `while c { … }` with neither `decreases` nor `fuel`. This lifts
  `docs/sequencing-surface-design.md` §6.2's "a carrier `while` takes
  `fuel`" for those carriers only.
- Whatever carrier-scope `for`/`while` lowering this needs
  (`List::for_m`, sequencing design §6.1), if it is not built yet.

## What it assumes from elsewhere
- **`lib/std/itree/coitree_rec.hthr`** owns `CoTree::rec`, `Returns`,
  fixpoint induction and `CoTree::get`. Assumed here: only that the surface
  elaborates onto them; no new proof rules.

## Done when

`Tm::whnf_co` (or another real customer) is written as a `partial fn` and
its soundness still goes through `rec_sound`; a `while` with no measure
checks in a `Partial` block, with a probe that returns at a count by `refl`
and a refusal for the same loop in a carrier without an iteration operator.

## Log

- 2026-11-03: Built (thread "Add the partial fn surface"); docs/partial-functions-design.md §9 and docs/sequencing-surface-design.md §18 record what departed. `partial fn` lowers in crates/elab/src/partial.rs to `f#body` (designated `f::body`) over the carrier of its calls, `f = CoTree::rec(…)` and `f_unfold`; several parameters nest in `Mutated`; `partial(E) fn` for events; refusals for a body that never calls itself, a self-call neither bound nor in tail position, and `f` passed as a value. `while c { … }` with no measure lowers in the parser to one `Iterate::then(init, step, k)` call, over the new `Iterate` class (itree.hthr) with instances at `CoTree<_>(E)`; refused with its reason in `Option` and in pure code. `CoTree` became a carrier first (codata-type-constructor-carrier, closed). Done-when: `Tm::whnf_co` is a `partial fn` and `whnf_co_sound` is `rec_sound` over `Tm::whnf_co::body` (kernel_whnf.hthr); `count(3)` returns 3 at a count by `refl` and the same loop is refused in `Option` (lib/_tests/std/itree/partial_fn_tests.hthr). Split out: [[partial-fn-tail-iter]] (the tail case to `iter`, which needs an iteration invariant rule) and [[partial-fn-use-site-refusal]].
