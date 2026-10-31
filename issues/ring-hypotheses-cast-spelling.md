---
title: ring(h, …) at CReal misses a combination when the goal spells ofRat of a sum
status: closed
labels: [tactics,arith,reals]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

Found proving `CReal::pade_err` (lib/std/num/float/pade.hthr). The same
identity, spelled two ways, behaves differently. Probe on master 5e26232
(imports as in `creal.hthr`):

```heather
// fails: "no combination of them (with polynomial multipliers) accounts for the difference"
theorem c6(x: Rat, X, S0, S1: CReal, z: X ≈ CReal::ofRat(1) + CReal::ofRat(x) * S0,
    o: X ≈ CReal::ofRat(-1) + CReal::ofRat(2) * S0 + CReal::ofRat(x) * CReal::ofRat(x) * S1):
    CReal::ofRat(2 - x) * X - CReal::ofRat(2 + x) ≈ CReal::ofRat(-(x * x) * x) * S1 { ring(z, o) }

// passes: the goal's left side spelled with the casts already pushed
theorem c8(…same hypotheses…):
    CReal::ofRat(2) * X - CReal::ofRat(x) * X - CReal::ofRat(2) - CReal::ofRat(x) ≈ CReal::ofRat(-(x * x) * x) * S1 { ring(z, o) }
```

The combination is `2·z - ofRat(x)·o`. With no hypotheses, `ring` proves
`ofRat(2 - x) * X ≈ ofRat(2) * X - ofRat(x) * X`. With one hypothesis it
also works (`ofRat(2 - x) * Y ≈ …` from `Y ≈ X`). So `ofRat` is pushed
through a sum in the goal, but the multiplier search over two hypotheses
misses when it has to. The Rat version of `c6` (no casts) passes.

Workaround used in pade.hthr: derive `X - 1 ≈ x S0` and `X + 1 ≈ …` with
one hypothesis each, then a `calc` with `CReal::sub_respects` /
`mul_respects` and a plain `ring`.

## Log

- 2026-10-31: Fixed. `ring`'s clearing substituted the cast definitions (`ofRat(2 - x)` as `2 - ofRat(x)`, and `ofRat(-1)` as `-1` through `map_neg`) in the target only; hypotheses kept the definition atoms, so the cleared target and the raw hypotheses never shared a reading and only the bounded joint search could link them (it did for c8, not c6). Each hypothesis now gets the same substitution (`substitute_definitions` in ring.rs), its multipliers handed back to the definitions' rows. Probes in lib/_tests/std/tactic/ring_field_tests.hthr; pade.hthr's calc workaround is `ring(z, o)` again.
