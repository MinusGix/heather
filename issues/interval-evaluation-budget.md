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

- a cheaper `down`. The width from comparisons against powers of two was
  tried and costs more fuel than halving (2026-10-31 log: a comparison is
  charged at its length). The shift as one division by `2^k` would be a
  long division too;
- a ratio enclosure the series can be given (`a` as a point times
  `recip(k+1)`), so a dyadic argument never divides by its own denominator;
- `exp(-a)` as `1/exp(a)` once that law is proved
  ([[elementary-functions-at-reals]]);
- split the proof where it helps: the enclosure equal to a literal interval
  by one `refl`, the rounding of that interval by another, joined by
  `round_box_correct`.

Perf rule: measure with `scripts/perf ab` and the counters, not seconds.

## Log

- 2026-10-31: Reciprocals by a checked guess (branch `claude/project-thread-50r7ej`).

  - **The kernel's fuel is not the `steps` column.** `ContextProgram::cancel_matching_prefix`
    charges each comparison or subtraction of two numerals its length
    (`eval.rs`, `self.fuel -= cancelled.inspected`), and `--timings` counts only
    evaluator steps. Measured with a local build that adds the inspections to
    `steps` and raises the fuel, the old `exp(1)` at binary64 used 1.65M and
    `exp(-3)` at binary32 1.13M.
  - **`ldiv` was most of it.** About 160 evaluator steps per numerator bit, and a
    reciprocal at `K = p + width(m)` divides all `K` bits. `Nat::pow2_div(K, d)`
    instead guesses `⌊2^K/d⌋` by doubling a remainder from `2^(width(d)-1)`,
    one quotient bit per step, and keeps the guess when `g·d <= 2^K < (g+1)·d`
    (`Nat::div_checked`), falling back to `ldiv` otherwise. The proofs see only
    `ldiv`'s two parts, so nothing about the loop is proved.
    `lib/_tests/std/num/nat_pow2_div_tests.hthr` checks it equals `ldiv`, that the guess is
    the quotient at every case but one, and the fallback.
  - **One quotient per point.** `Interval::of_rat` took `recip` of a point,
    which tests both signs and divides once per bound. `Interval::recip_point`
    divides once (`recip_point_has` is `recip_bounds`).
  - **Tried and dropped: the width by comparisons.** Ten comparisons against a
    literal table of `2^(2^j)` beat `width`'s halving in evaluator steps but
    lose in fuel, because each comparison is charged at the mantissa's length.

  Fuel, before → after (2^20 = 1,048,576):

  | value | before | after |
  |---|---|---|
  | exp(1), binary32 | 658K | 329K |
  | log 3, binary32 | 936K | 464K |
  | exp(-3), binary32 | 1,134K | 624K |
  | exp(10), binary32 | 1,820K | 860K |
  | exp(1), binary64 | 1,652K | 747K |
  | exp(0.5), binary64 | 1,395K | 644K |
  | log 3, binary64 | 2,807K | 1,204K |
  | exp(-3), binary64 | 2,660K | 1,328K |

  `exp_neg_three_32` and `exp_one_64` are now `refl` tests in
  transcendental_tests.hthr. Still over: binary64 log, because the atanh
  ratio's divisor is `(A + B)^2`, about 110 bits, and every guess step compares
  at that length, and binary64 exp at negative arguments. What is left in the
  order it would pay: rounding's width and shift (six per series term); the
  ratio's divisor length (an atanh ratio as a point times `recip(…)` of a short
  number, or `a` times `recip(k + 1)` for exp); `exp(-a)` as `1/exp(a)`.
