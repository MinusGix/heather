---
title: Hedberg: unique identity proofs for a type with decidable equality
status: open
labels: [library,logic]
area: mathematics
milestone: [none]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). The library has no proof that a type with decidable equality has unique identity proofs (Hedberg's theorem): for `dec: (a, b: A) → Or<a = b, ¬(a = b)>`, every `p: a = a` is `refl`. Nothing in `lib/` states it (`grep -i "uip\|hedberg"` finds nothing).

The customer it was found for: a family indexed by codes (a data universe of shapes, `lib/_tests/lang/ownership/typed_steps_tests.hthr`) whose proofs compare two steps out of one source. Matching the first step fixes the source code; the second step is then at a constructor-headed index, which the elaborator does not invert (an index constructor with payload arguments), so the proof matches it under a convoy `CIx::src(st) = SSeq(x)`. The arm holds `e: SSeq(y) = SSeq(x)`; injectivity gives `y = x`, and the goal still transports along `e`, which is `refl` only by UIP at the code type. With UIP that case closes; without it, no such proof can be finished. Strict equality (`sEq`) has UIP definitionally but no eliminator since `transp` was removed, so it does not help.

It is a cheap lemma: the standard proof needs only `J` (a constant endomap on `a = b` built from `dec`, and every path is that map's value composed with the inverse of its value at `refl`).

## Done when

`lib/std/core` (or wherever decidable equality lives) states Hedberg's theorem over a decider in the library's shape, with a probe instantiating it at a declared inductive with a `same` decider (`Nat`, and a two-constructor recursive type).
