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
(`exp_no_tries`). Enough tries always succeed for a real clear of the
rounding grid, read through enclosures that narrow (next section). For exp
and log that clearance is the Padé gap.

**The ends are rounded in a window** (`round_dyadic_win`, through
`round_hex`). `round_dyadic` works in half-units of 2^qmin, which is a
1075-bit count near one at binary64. That size is past the evaluator's depth
budget. The literal path had already solved the problem with a window
(window.hthr), so a dyadic is rounded the same way as a hex literal. A
negative dyadic rounds its magnitude under the conjugate mode.

## The search ends

Added the same day by
[float-round-real-termination](../issues/float-round-real-termination.md).
The probes are in
[`round_real_tests.hthr`](../lib/_tests/std/num/float/round_real_tests.hthr).

```heather
fn Format::round_real_apart(self F: Format, mode: Mode, e: Enclosed,
    narrow: e.Narrows(F.prec() + 16, F.prec() + 16, 16), off: F.OffGrid(e.x)) → Float(F)
theorem Format::round_real_apart_correct(…): RoundsToReal(F, mode, e.x, F.round_real_apart(mode, e, narrow, off))
```

This is Ziv's search with no fuel and no `Option`. It takes two proofs.

**The gap is stated against the grid, not per mode.** Every breakpoint of
every mode is a half-unit grid point `F.grid(m)`. A float's value is one
(`Finite::val_grid`), so is the midpoint of two neighbours (`mid_sum`), and
so is the overflow threshold `F.grid(F.ovf_h())`. So rounding is constant on
each open grid cell, and `round_h` with the sticky bit set already computes
the constant (`cell_rounds`; a negative cell goes through the conjugate
mode). `F.Cell(x, h, k)` says that the real `x` lies in cell `h`, at least
`2^-k` clear of both its ends. `F.OffGrid(x)` is `∃ h k, F.Cell(x, h, k)`.

This is stronger than apartness from one mode's breakpoints. It also rules
out the grid points that no mode breaks at, such as the floats themselves
under a nearest mode. It was chosen because it needs no case per mode, and
`Approx` already speaks its language. For the reals it is meant for it is
just as true: exp and log at floats are irrational, apart from their exact
cases. The cost is only in the bound. A real near a grid point that is not a
breakpoint gets a small `k`, so the try count proved is larger, while the
search still stops as soon as the two ends agree. The per-mode `Breakpoint`
and the classical `Placed` of §6 are not built. Nothing needs them yet.

**Narrowing is the other hypothesis.** `e.Narrows(n, p, step)` says that for
every `k` some try's box is narrower than `2^-k`. It is an existence, so the
try count computes from it. `Enclosed::narrows_of` reduces it to "narrower
than `2^-k` from some index on, at any precision". `CReal::enclosed(x)`, a
real's own boxes `x.seq(n) ± 2^-n`, narrows that way
(`CReal::enclosed_narrows`).

**The chain.**

- `round_box_cell`: a box with both ends inside one cell rounds both ends
  to `Same` floats (`rounds_unique` against the cell's rounding). `agree`
  reads that as `True` (`Float::agree_of_same`, the converse of
  `same_of_agree`), so the box answers `Some`.
- `round_box_of_cell`: a box around `x` narrower than `2^-k` has both ends
  in `x`'s cell. This is four `linarith` steps.
- `round_enclosed_some`: a try `t` whose box answers ends the search at
  or before `t`, given more than `t` tries. The schedule is read through
  `Enclosed::try_at`, which unfolds as `round_enclosed` does, so no
  multiplication `n + step·t` appears.
- `round_enclosed_ends` puts them together, with
  `round_apart_tries = 1 + (the narrowing's try for the gap's k)`.
  `round_real_ends` restates it for `round_real` itself.

At 1/3 in binary32 (2^150 = 3h + 1, so k = 152), `round_real_apart` gives
0x3EAAAAAB for nearest and up and 0x3EAAAAAA for down, by `refl`. The proof
term is evaluated through the theorems. The try count is 155, though the
search stops at its first try.

What exp and log still owe is
[exp-log-grid-gap](../issues/exp-log-grid-gap.md). Their gap is the Padé
bound, and their series boxes must be shown to narrow.

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
| exp(-3) | binary32 | 0x3D4BED86 |
| exp(1) | binary64 | 0x4005BF0A8B145769 |

**Cost.** Each is evaluated under the kernel's fixed fuel of 2^20. The fuel
counts evaluator steps and, for every comparison or subtraction of two
numerals, the length of the numbers compared. As of
[interval-evaluation-budget](../issues/interval-evaluation-budget.md), a
binary32 value takes between a third and two thirds of it and exp(1) at
binary64 about seven tenths. Before that round, the ratios' reciprocals were
long divisions over every bit of `2^K`. Now they are a guessed quotient
checked by two comparisons (`Nat::pow2_div`). That halved every cost and
brought exp(-3) at binary32 and exp(1) at binary64 inside the fuel.

Where the fuel still goes:

- **Every interval operation ends in `Dyadic::down`/`up`.** Their width and
  shift halve once per bit. Comparisons against a table of powers of two
  were tried for the width and cost more fuel: a comparison is charged by
  its length.
- **Each reciprocal's guess compares once per quotient bit,** at the
  divisor's length. log's ratio divides by `(A + B)^2`, twice a mantissa's
  width, so log 3 at binary64 is still over the fuel.
- **Alternating series take the four-corner product every step.** Their
  cancellation also costs a second try. exp(-3) at binary64 is over too.

## Left out

- **IEEE specials:** done since, as `Float::exp` and `Float::log` over every
  float ([float-exp-log-specials](../issues/float-exp-log-specials.md)):
  exp(±∞), exp(±0) = 1 exactly, log(±0) = -∞, log of a negative number and
  log(-∞) invalid, NaN in, NaN out. log(1) = +0 exactly is still the search
  ([float-log-one-exact](../issues/float-log-one-exact.md)).
- **The Padé gap for exp and log**, and narrowing of their series boxes:
  what `round_real_apart` asks of them
  ([exp-log-grid-gap](../issues/exp-log-grid-gap.md)). The search's end
  itself is the section above.
- **Argument reduction for exp:** a large argument starts its series far out
  ([interval-log-and-reduction](../issues/interval-log-and-reduction.md)).
- **The generic `RoundsTo` over an ordered field:** the transfer lemma of §6.
  `RoundsToReal` is its `CReal` instance, stated without it.
- **Faithful rounding without side conditions** (§6): not built. Ziv's
  search answers the correct-rounding question directly.
