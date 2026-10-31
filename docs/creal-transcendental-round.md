# Compression, correct rounding of reals, and the first transcendentals

Date: 2026-10-31. Closes
[creal-compress-and-transcendentals](../issues/creal-compress-and-transcendentals.md).
It builds on the dyadic rate of [creal-dyadic-round.md](creal-dyadic-round.md)
and starts two submilestones of `math-float`: `float-reals` and
`float-transcendental` ([floating-point-design.md](floating-point-design.md)
§6, §8). The code:

- `CReal::compress` in [`creal.hthr`](../lib/std/num/creal.hthr);
- the relation and the search in
  [`round_real.hthr`](../lib/std/num/float/round_real.hthr);
- `CReal::log_rat` in [`elementary.hthr`](../lib/std/num/float/elementary.hthr);
- `Format::exp_fin` and `Format::log_fin` in
  [`transcendental.hthr`](../lib/std/num/float/transcendental.hthr).

The probes are in
[`transcendental_tests.hthr`](../lib/_tests/std/num/float/transcendental_tests.hthr)
and [`creal_tests.hthr`](../lib/_tests/std/num/creal_tests.hthr).

```heather
theorem exp_one_32(): binary32().exp_fin(NearestEven, one32(), 4) = Some(Fin(Finite(False, 11401300, 127, trivial))) { refl }

theorem e_rounds(): RoundsToReal(binary32(), NearestEven, CReal::exp_rat(one32().val()), Fin(Finite(False, 11401300, 127, trivial))) {
    binary32().exp_fin_correct(NearestEven, one32(), 4, Fin(Finite(False, 11401300, 127, trivial)), exp_one_32())
}
```

The first theorem is the kernel computing e to binary32 (0x402DF854). The
second is what that value means: it is the correct rounding of the real
`exp(1)`.

## Compression

Every `CReal` operation rounds its term to n+1 bits, except a sum, a
negation and a limit. Those pass their arguments' dyadics on unchanged, and a
real built by hand from a sequence can have terms of any size.
`x.compress()` is O'Connor's remedy. It reads `x` one index further out and
floors the result to n+1 bits:

```heather
fn CReal::compress(self x: CReal) → CReal { CReal::rounded(λ n => x.at(n + 1), λ m n => x.regular(m + 1, n + 1)) }
theorem CReal::compress_exp(self x: CReal, n: Nat): x.compress().seq(n).exp = -(n + 1).int() { refl }
theorem CReal::compress_same(self x: CReal): x.compress() ≈ x
```

The proof is Bishop's bound: one rounding plus x's own regularity add up to
2 · 2^-n. Compression is opt-in, and nothing else had to change.

After the dyadic round it matters less than it did in the design thread,
where it was proposed as a stopgap before that round. Today it is the tool for
long chains of sums, for limits, and for sequences that clients build.

## The relation at `CReal`

Rounding a real is not a function. No finite approximation decides which side
of a breakpoint the real lies on. What is always meaningful is a relation:

```heather
fn RoundsToReal(F: Format, mode: Mode, x: CReal, r: Float(F)) → Type {
    ∃ lo: Rat, ∃ hi: Rat, CReal::ofRat(lo) <= x ∧ x <= CReal::ofRat(hi) ∧ ((q: Rat) → lo <= q → q <= hi → RoundsTo(F, mode, q, r))
}
```

In words: some rational interval around x rounds to r throughout.

- **At a rational it is `RoundsTo`.** The degenerate interval
  `[q, q]` gives `rounds_real_of_rat`, and `rounds_real_rat` goes back through
  `CReal::le_of_ofRat_le`.
- **It is unique up to `Float::Same`** (`rounds_real_unique`). Two intervals
  around one real overlap, and their larger lower end lies in both.
- **It respects `≈`** (`rounds_real_respects`).
- **Classically, it is the usual meaning.** A real that is not a breakpoint
  lies inside an open cell where rounding is constant. A real that is one is
  `≈` a rational, and the degenerate interval serves.

The design (§6) states the relation over any ordered field through a
transfer lemma. That generic `RoundsTo` is still open. This round's relation
is the `CReal` reading, stated with the rational relation that already
exists, so no clause of `RoundsTo` had to be restated.

## Ziv's search

`Format::round_box(mode, I)` rounds both ends of a dyadic enclosure. When the
two roundings agree, everything inside the enclosure rounds to them:

- rounding is monotone (`rounds_mono`), so a rational between the ends
  rounds between the two roundings;
- a float squeezed between two agreeing floats has their value
  (`Float::same_of_squeeze`);
- `RoundsTo` depends only on the value, up to `Float::Same`
  (`rounds_of_same`). Its `NearestEven` case needs canonical floats of one
  value to share a significand (`Finite::mag_of_same_val`).

`Float::agree` decides agreement, and `same_of_agree` reflects it.
`round_enclosed` refines an `Enclosed` real 16 bits at a time, both its
index and its precision, `tries` times. `round_real` starts at the format's
precision plus 16 guard bits. Its correctness theorem has no side condition:

```heather
theorem Format::round_real_correct(self F: Format, mode: Mode, e: Enclosed, tries: Nat, r: Float(F),
    is: F.round_real(mode, e, tries) = Some(r)): RoundsToReal(F, mode, e.x, r)
```

`None` means the tries ran out. It never means a wrong answer
(`exp_no_tries`). Whether enough tries always succeed is the apartness
theorem of §6, and for exp and log it is the Padé gap. Both are
[float-round-real-termination](../issues/float-round-real-termination.md).

**The ends are rounded in a window** (`round_dyadic_win`, through
`round_hex`). `round_dyadic` works in half-units of 2^qmin, which is a
1075-bit count near one at binary64. That size is past the evaluator's depth
budget. The literal path had already solved the problem with a window
(window.hthr), so a dyadic is rounded the same way as a hex literal. A
negative dyadic rounds its magnitude under the conjugate mode.

## exp and log

`Format::exp_fin(mode, f, tries)` is Ziv's search over `CReal::exp_box` at
`f.val()`, which is the series' own `Enclosed` leaf.

`log` at a positive rational is new:

```
log(a/b) = 2·atanh((a' - b')/(a' + b')) + e·log 2,     a/b = (a'/b')·2^e
```

- **The binade.** `Binade::of` scales the smaller of a and b by the
  difference of their bit widths, so the two land in one binade.
  `Nat::pow_width_le` (new in `nat.hthr`) pairs with `lt_pow_width` to place
  each number in its binade.
- **Every ratio is at most 1/2.** Each of a' and b' is below twice the other,
  so with t = (a' − b')/(a' + b') we get 2t² ≤ 1/2. Then every ratio
  t²(2k+1)/(2k+3) is at most 1/2 from the first term on (`Series::atanh_close`).
- **Writing the ratio for `omega`.** The ratio is spelled in monomials,
  `2(Xk) + X` over `2(mk) + 3m + 2k + 3`, because `omega` reads products as
  atoms and does not distribute them.
- **log 2** is 2·atanh(1/3).
- **The enclosure.** The real is `CReal::log_expr(a, b)`, the checker
  expression `RAdd(RBox(binade series), RMul(RRat(e), RBox(log 2)))`.
  `RealExpr::enclosed` (new in `creal_interval.hthr`) makes a well-formed
  tree its own `Enclosed` leaf. `CReal::log_rat` is its value at
  `q.num.natAbs() / q.den`.

`log_rat` is *defined* as this sum. That it is exp's inverse is a law, owed in
[elementary-functions-at-reals](../issues/elementary-functions-at-reals.md)
with the rest. So `log_fin_correct` says "the correct rounding of
`CReal::log_rat(f.val())`", which is log by its standard series.

## What computes today

Each value below is a `refl` theorem. Each was compared against a 200-digit
reference rounded exactly.

| value | format | result |
|---|---|---|
| exp(1), nearest, down, up | binary32 | 0x402DF854, 0x402DF854, 0x402DF855 |
| exp(0.5), exp(-0.5) | binary32 | correct |
| exp(1) | binary16, bfloat16 | correct |
| log 2, log 3, log 10, log 1.5, log 0.5 | binary32 | correct |

**Cost.** One of these uses between a quarter and nine tenths of the kernel's
fixed 2^20-step budget. `exp(-3)` at binary32 and `exp(1)` at binary64 run out
of steps.

Where the steps go:

- **Every interval operation ends in `Dyadic::down`/`up`.** Their bit-by-bit
  width and shift are a few thousand steps at 80 bits, and a series step is
  four or five such operations.
- **Each ratio is a long division by the argument's unreduced denominator.**
- **Alternating series take the four-corner product every step.** Their
  cancellation also costs a second try.

The directions are in
[interval-evaluation-budget](../issues/interval-evaluation-budget.md).
binary64 waits on them. Nothing in the proofs does.

## Left out

- **IEEE specials:** exp(±∞), log(0), log of a negative number, and NaN
  ([float-exp-log-specials](../issues/float-exp-log-specials.md)).
- **Termination:** a total `round_real_apart` from the Padé gap
  ([float-round-real-termination](../issues/float-round-real-termination.md)).
- **Argument reduction for exp:** a large argument starts its series far out
  ([interval-log-and-reduction](../issues/interval-log-and-reduction.md)).
- **The generic `RoundsTo` over an ordered field:** the transfer lemma of §6.
  `RoundsToReal` is its `CReal` instance, stated without it.
- **Faithful rounding without side conditions** (§6): not built. Ziv's
  search answers the correct-rounding question directly.
