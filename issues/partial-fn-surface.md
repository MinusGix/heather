---
title: partial fn surface, and while with no measure in carriers that iterate
status: open
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
