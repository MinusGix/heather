---
title: Stochastic rounding
status: open
labels: [mathematics,floating-point,probability]
area: mathematics
milestone: [math-float]
created: 2026-11-25
updated: 2026-11-25
---

P3109 has stochastic rounding (SR) in three variants that differ in how a
finite number of random bits is used ([[float-p3109]]; FLoPS §2 and §3.3,
after Fitzgibbon and Felix, ARITH 2025). Design §5.4 left SR for the ML
milestones because it is a distribution over the two neighbours, not a
function.

## Two layers

1. **Pointwise, now.** SR with `N` random bits is a function of `x` and an
   `N`-bit draw. Every outcome is a faithful rounding, so every bound that
   holds for faithful rounding holds for each outcome; state that and
   nothing else needs probability. It is also the form an implementation
   takes, so the three variants are three functions.
2. **In expectation, later.** FLoPS proves the cheapest variant has bias
   exactly `-2^-(N+1)`, the second is unbiased for every exact input, and
   the third stays unbiased for inputs with finitely many bits, and that the
   unbiased variants have `O(√n)` root-mean-square error over `n`
   independent roundings. The first three are sums over the `2^N` draws, so
   they are finite expectations: [[finite-probability]] is enough, and at a
   concrete format they evaluate. The `√n` bound needs independence and
   variance from the same layer.

SR is faithful but not monotone; FLoPS split Flocq's single rounding class
into separate `Faithful` and `Monotonic` ones for this reason. Design
§5.4's `Rounding` record should keep those as separate fields for the same
reason.

## What it assumes from elsewhere

- **[[finite-probability]]** owns finitely supported distributions and
  expectation. Assumed here: only an expectation over a uniform finite draw.

## Log

- 2026-11-25: Pointwise layer landed (design §6): `round_sr_a`/`_b`/`_c` follow the report's `RoundAway` rules, with `ν·2^N` computed exactly from the truncation; every draw is faithful (`round_dir_faithful`). `Nat::count_away_all` gives variant A's count of away-steps (`⌊ν·2^N⌋` of `2^N`). Still open: the expectation statements and the `O(√n)` bound, on [[finite-probability]]; and the variants through `project`'s saturation.
- 2026-11-25: The three variants now also go through the saturation modes (`project_sr_a/b/c`, faithful by `project_dir_faithful`), which closes `p3109-projection`. What this issue still owns is the expectation layer on [[finite-probability]].
