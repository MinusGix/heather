---
title: Ownership: the interfaces of §21 as modules (total steps, values, the body and its meaning)
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first package of the real ownership modules: the interfaces of `docs/language/ownership-design.md` §21, written as modules of definitions over which the checker, the two readings and `check_sound` are later built once (§20.6 step 2). §21 is the specification; a definition that cannot be written as §21 states it goes back to the coordinating session and is not adjusted in the module.

## Scope, in order, each landed before the next

1. **The total step model, in place** (§21.1 last bullet, §21.5 probe 1): `steps.hthr`'s `StepModel` and `StepModelLaws` become a total read `at`, a total modification `over`, a Boolean fit of a step to an owner, laws where the step fits and relative to what was read there; `Steps::apart_sound` re-proved over it.
2. **Values** (§21.1): `Shape`, the type environment and `El`, `Struct` (sharing class; opaque, record, sequence) with each kind's laws, `Dyn`, and `Dyn`'s instance of the total step model from the structures' laws alone. Instances by hand: a user record; `List<A>`, `[A; n]` and `Bytes(n)` as sequences each spelling its accessor's bound; a word type that is not `Nat`. Probes: reads under each instance's bound are the source's term by conversion; `value_steps.hthr`'s customers restated at `Dyn`.
3. **The body and its meaning** (§21.2, §21.3 first two bullets): `Place`, `Stmt`, `Body` (`Ret`, `Yield`, `Do`, `Join`, `Jump`), `Func`, one environment of `Dyn`s, the meaning in continuation form over a world of callee meanings; the pins of `coded_tests.hthr` restated, §21.5 probe 3, a `while` with `decreases` and a `for`.
4. **§21.5 probe 2**: one environment against two, at doubling sizes, with a word type other than `Nat`.
5. **The remaining interfaces as definitions only** (§21.3 third bullet, §21.4): level 2's heap, objects with holes, canonical references, the run's outcome; the residual kinds, the verdict's tree, and the statements of a function's safety and of `check_sound` as `Type`-valued definitions, each stated at one small function.
6. **Retire what this replaces**: `value_steps.hthr`, `coded.hthr` and their tests when covered; `PathLawsOn` and `KeepsFit` from `lib/std/machine/path.hthr` if nothing else uses them.

`call_check.hthr` and `place_check.hthr` are not edited.

## What it assumes from elsewhere

- **[[ownership-coded-values]]**: the sixth experiment, whose result (§20.5, §18.4 item 4) fixes the value sort.
- **[[ownership-join-chain-cost]]**: the one known non-linear shape.
- **[[ownership-write-bounds]]**, **[[ownership-pin-after-join]]**, **[[ownership-world-depth-zero-postconditions]]**: requirements on what is built over these interfaces.

## Done when

Items 1 to 6 have landed with `scripts/test --pr` green, or the package stopped after a landed item with what remains stated; `ownership-design.md` has a §22 "The interfaces as built".
