---
title: Formats with one bit of precision
status: closed
labels: [mathematics,floating-point]
area: mathematics
milestone: [p3109-values]
created: 2026-11-25
updated: 2026-11-25
---

`Format` requires `frac_ok: 1 <= frac` (precision at least two). P3109 has
precision-one formats ([[float-p3109]]): every nonzero value is `±2^e`, and
the trailing bits of the encoding are the exponent's. Relax the bound to
`frac: Nat`.

## What breaks

- **The nearest-even tie rule.** `Finite::NearestEven`
  (`lib/std/num/float/round.hthr`) breaks a tie toward `Nat::Even(f.mag)`.
  At precision one every nonzero significand is `1`, so at a tie between two
  nonzero neighbours neither is even, no float satisfies `NearestEven`, and
  `round::correct` would be false. P3109 breaks such ties by the parity of
  the *exponent* (FLoPS §2, §3.3). The uniform reading is "the neighbour
  whose encoding ends in 0": the significand's last bit when `frac >= 1`,
  the exponent field's last bit when `frac = 0`. Check the standard's exact
  wording (biased or unbiased exponent; the tie between zero and the least
  subnormal) before stating it.
- **Lemmas that use the bound.** `Format::two_le_half` (`float.hthr`; used
  in `float.hthr`, `round.hthr`, `error.hthr`, `window.hthr`) and the
  evenness of `2^frac` at `round.hthr:562` (the carry into the next
  binade lands on an even significand). Each use either takes `1 <= frac`
  as a hypothesis or gets a precision-one case. `Finite::veltkamp` already
  bounds its split by `s <= frac`, so it is vacuous there.
- **The standard model.** `u = 2^-prec` still holds at `prec = 1`
  (`u = 1/2`); check that `error.hthr`'s proofs do not use `prec >= 2`
  beyond `two_le_half`.

## The rounding routine

`Format::round_h` picks the neighbours from the half-unit count `h`, which
fixes the exponent, so the exponent-parity tie fits it: the exponent is
known when the tie is broken. FLoPS needed a rounding operator of type
`ℤ → ℝ → ℤ` (exponent first) for this reason, against Flocq's `ℝ → ℤ`
(§3.3).

## Tests

A precision-one format (P3109's signed and unsigned `K = 8, P = 1`) in
`lib/_tests/std/num/float/round_tests.hthr`: a tie between `2^e` and
`2^(e+1)` for both parities of `e`, the tie between zero and the least
value, overflow per `Specials`. Negative control: the tie rule read as
significand parity has no witness at the tie (a `¬ ∃` theorem).

## What it assumes from elsewhere

- **[[float-p3109]]** owns how P3109 formats become `Format`s. Assumed
  here: only that some of them have `frac = 0`.

## Log

- 2026-11-25: LANDED (docs/library/float-p3109-design.md §5). `frac_ok` is gone; ties go to the even code (`Format::lsb`: the significand's last bit with fraction bits, the biased exponent's at precision one), proved through `lsb_step`/`lsb_carry`. Uses of the old bound: `two_le_half` now takes `1 <= frac`; `half_even` likewise; `u_le_gamma` takes `1 < u_den` (a directed mode at precision one has `u = 1`). Found: a window an odd number of binades up flips precision-one ties, so `widen` falls back there (`win_par`). Tests in `lib/_tests/std/num/float/p3109_tests.hthr`: ties at `2^e`/`2^(e+1)` of both parities, the zero tie, and the negative control (both neighbours of the tie at 6 in Binary8p1se have significand 1).
