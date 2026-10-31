---
title: Make interval enclosures cheap enough to round binary64 exp and log by evaluation
status: open
labels: [mathematics,float,performance]
area: mathematics
milestone: [float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

A correctly rounded value is proved by `refl` on Ziv's search
(lib/std/num/float/round_real.hthr), so its whole cost is kernel evaluation
under the fixed 2^20-step budget. binary32 exp and log at moderate arguments
fit (`exp(1)` about half the budget, `log 3` most of it); `exp(-3)` at
binary32 and `exp(1)` at binary64 run out (`OutOfFuel`).

Where the steps go (probes of 2026-10-31, counted with `--timings`):

- every interval operation ends in `Dyadic::down`/`up`, and `down` on an
  80-bit mantissa is a few thousand steps: `Nat::width` halves bit by bit and
  `Nat::shr` halves `k` times. A series step is four or five such operations,
  so twenty-odd thousand steps;
- `Interval::of_rat` of each ratio is a reciprocal by long division at `p`
  bits, plus the ratio's own denominator: a float argument's value is an
  unreduced `m / 2^k`, so `exp`'s ratio `a/(k+1)` divides by `2^k (k+1)`;
- alternating series (exp at a negative argument) take the four-corner
  product path every step, and their cancellation costs a second try.

Directions, cheapest first:

- a cheaper `down`: the width from comparisons against powers of two (which
  the kernel's run arithmetic does in a step) and the shift as one division
  by `2^k`, if the long division of a power of two is as cheap as its probe
  suggests;
- a ratio enclosure the series can be given (`a` as a point times
  `recip(k+1)`), so a dyadic argument never divides by its own denominator;
- `exp(-a)` as `1/exp(a)` once that law is proved
  ([[elementary-functions-at-reals]]);
- split the proof where it helps: the enclosure equal to a literal interval
  by one `refl`, the rounding of that interval by another, joined by
  `round_box_correct`.

Perf rule: measure with `scripts/perf ab` and the counters, not seconds.
