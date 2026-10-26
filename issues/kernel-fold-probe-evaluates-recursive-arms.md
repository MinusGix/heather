---
title: Stop the Nat fold probe from re-evaluating recursive match arms
status: closed
labels: [kernel,perf]
area: kernel
created: 2026-10-25
updated: 2026-10-26
---

A `match` on a `Nat` whose arms make a recursive call of an *enclosing*
recursion costs time exponential in that recursion's depth when the
scrutinee is a literal and the result is not a `Nat`:

```
fn f(p: Prog) → Bool { match p { Start => True, At(before, name, _) => match name { Zero => f(before), Succ(_) => f(before) } } }
```

`f` over a ten-item program whose names are all `1` runs out of a
declaration's fuel; the same function returning a `Nat` is a hundred steps,
and so is `f` with the inner `match` on `name.is_zero()`.

## Why

A literal is a run (`Val::NatRun`), and a fold over a run first classifies
its step (`eval/runs.rs`'s `fold_run`, `eval/probe.rs`'s `classify_step`):
the step is applied to neutral `k` and `ih` and driven to its δ-transparent
weak head value. The inner `match`'s step is the `Succ` arm, which calls
`f(before)`, so the probe evaluates the whole recursive call. A `Bool` is
no affine tree, so the class is `Opaque` and the fold then takes the
ordinary step, which evaluates `f(before)` again. Two evaluations per level
is `2^depth`. The class is memoized per closure, but each level's step is a
different closure (it captures `before`), so the memo never hits. (A `Nat`
result classifies as a literal tree and the ordinary step is skipped, which
is why the `Nat` variant is cheap.)

## Where it bit

`x86_64_asm_runs`'s `names_unique` and `fresh_names` were spelled with
exactly that inner `match name { Zero => …, Succ(_) => … }`. A program with
ten named labels ran a declaration out of fuel; the loops-anywhere round
(issues/function-ir-loops-anywhere.md) respelled both on `name.is_zero()`
(`Nat::is_zero`'s comment says why). Other library functions with the shape
are unaudited.

## What would fix it

- The probe charges ordinary fuel and spends it on work the fold redoes.
  Bound the probe's own evaluation (a small budget of its own; `Opaque` when
  it runs out, which is always sound), so a step whose weak head value is
  an arbitrary computation is declined cheaply.
- Or skip the probe where it can buy nothing: a run of one successor folds
  in one ordinary step whatever its class.
- Either way, a kernel test pinning the cost: the `Bool` variant above at a
  depth where `2^depth` steps would exceed the fuel.

The verdict's soundness is not in question (`hih-km-probe`); this is cost.

## Log

- 2026-10-26: FIXED in the kernel, by the second route generalized: a step in which `ih`
  does not occur is not probed (`FoldClass::Direct`, `eval/probe.rs`'s last
  module section). Such a step is no algebra: the fold's one ordinary step is
  the whole fold at any run, so no class could do better. Every shape this
  issue names is one: a `match` on a literal inside an enclosing recursion
  never reads the fold's `ih`, its arms being the *enclosing* recursion's
  calls. The test is syntax (`bounds::ignores_innermost`, a `uses` bit mask
  beside `LocalUse::bound`), but it only decides whether to probe; the
  ordinary step is the fold's definition, so there is nothing for the kernel
  model to preserve.

  The cost was worse than the issue said: four evaluations of the arm per
  level, not two (uniform probe, peeled probe, the bit-transducer probe's gate,
  then the ordinary step), so a walk whose arm recursed before reading the
  predecessor ran out of fuel at eight items. Probes in
  `lib/_tests/std/num/nat_tests.hthr`: 64-item walks with names 1, 10^6 and
  0…63, recursing before or after reading the predecessor, all out of fuel on
  master and under 2K steps now. Across the library one opaque probe in
  `lib/_tests` alone had spent ~977K steps on an `ih`-free step.

  The first route (a probe budget) was tried and dropped: it fixes the walks
  (linear, at the budget per level), but measured across the library, real
  affine probes cost up to ~32K steps, mostly forcing environment thunks that
  the fold then reuses (`add(ih, a)` with `a` computed), so any budget small
  enough to matter declines real algebras into unary folds.

  Workarounds undone: `names_unique`/`fresh_names` match on `name` again and
  `Nat::is_zero` is gone. `Nat::ldiv` was not this issue: it is linear in the
  numerator's bits, and its failure past ~700 bits is `NATIVE_DEPTH_LIMIT`
  (one evaluator re-entry per quotient bit), [[eval-native-frame-size]].

  Behaviour change to watch: an `ih`-free step whose value was a literal used
  to classify as an affine `Lit`, which also made `step_elim` unfold a glued
  scrutinee eagerly; `Direct` does not, like `Opaque`. Not exercised: a step
  that reads `ih` and runs an enclosing recursion before reading it is still
  probed in full; no library step was seen doing so.
