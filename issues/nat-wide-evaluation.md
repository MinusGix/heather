---
title: Evaluate Nat::pow and Nat::ldiv at binary64 sizes
status: open
labels: [nat,evaluation,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-10-26
updated: 2026-10-26
---

Two of `nat.hthr`'s workhorses stop evaluating near a thousand bits, which
is where binary64 lives (its grid is `2^-1075`, its overflow limit
`2^1024`). Probes on master at 9486d1a, `heather check --cache`, release:

- **`Nat::pow(2, n)` fails from `n` ≈ 1024.** `pow(2, 1020)` evaluates,
  `pow(2, 1030)` is `OutOfFuel` in a few thousand steps. `pow` is
  `a.pow(k) * a`, one native evaluator re-entry per exponent step, so it
  meets `NATIVE_DEPTH_LIMIT` ([[eval-native-frame-size]]) rather than the
  fuel. Binary exponentiation (halve the exponent, square, multiply by the
  low bit) evaluates `2^2047` and `10^300` in about ten milliseconds each.
- **`Nat::ldiv` fails on a 1050-bit numerator.** `ldiv_fuel` matches
  `n { Zero => …, Succ(k) => … Succ(k).half() … }` inside its recursion and
  returns a `DivMod`, which is the pattern
  [[kernel-fold-probe-evaluates-recursive-arms]] describes. The same
  division spelled with `n.is_zero()`, the low bit as `n - n.half() * 2`
  and the remainder doubled as `r * 2` divides `2^1050 · 12345` by
  `10^300` in about a second, with fuel bounded by the quotient's width
  rather than the numerator's.

Consequence: `Format::round_rat` and `round_h` do not evaluate at binary64
at all (`rat_q` is `pow(2, 1075)`, `limit_h` is `pow(2, 2046)·…`, and
`e_of` searches 2046 exponents over a 1075-bit `h`). binary32 evaluates.

## Proposal

- `Nat::pow_sq` (binary exponentiation) with `pow_sq = pow`, and use it
  wherever a library function raises to a format-sized exponent.
- `ldiv`'s recursion respelled as above, keeping `ldiv_div`/`ldiv_mod`;
  plus a quotient-width-fuelled variant whose spec assumes `n < d · 2^k`.

The float-literal round ([[float-literal-entry]]) needs both and adds what
it uses; the rest of the library's call sites are this issue.
