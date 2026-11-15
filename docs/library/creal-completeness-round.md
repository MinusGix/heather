# Regular Cauchy reals: completeness

Date: 2026-10-26. The last item of
[regular-cauchy-reals](../../issues/regular-cauchy-reals.md): the diagonal
completeness construction, in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr)
(the section at the end), with four rational facts added to
[`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The probes are in
[`lib/_tests/std/num/creal_tests.hthr`](../../lib/_tests/std/num/creal_tests.hthr).
It closes the issue.

```heather
fn CReal::Regular(xs: Nat → CReal) → Type {
    (m, n: Nat) → (xs(m) - xs(n)).abs() <= CReal::ofRat(Rat::inv_succ(m) + Rat::inv_succ(n))
}

fn CReal::Limit(xs: Nat → CReal, y: CReal) → Type {
    (n: Nat) → (xs(n) - y).abs() <= CReal::ofRat(Rat::inv_succ(n))
}

theorem CReal::complete(xs: Nat → CReal, h: CReal::Regular(xs)): ∃ y: CReal, CReal::Limit(xs, y)
```

## The statements

A sequence of reals is regular at the same rate a real's own terms keep:
its m-th and n-th reals are within 1/(m+1) + 1/(n+1). It converges to y at
that rate too, the n-th real within 1/(n+1) of y. Both are stated with the
real distance `(x - y).abs()` against an embedded rational, so they read as
the usual definitions and not as facts about terms. `CReal::abs` is new: the
termwise size, regular by the reverse triangle inequality
(`Rat::abs_sub_abs_le`), and it respects `≈`.

Fixing the rate in the type is the same choice the representation made. A
sequence with its own modulus can be reindexed into a regular one, so
nothing is lost, and no estimate carries a modulus parameter. Whether the
general modulus form belongs in an interface is
[real-completeness-interfaces](../../issues/real-completeness-interfaces.md)'s
question, logged there.

## The diagonal

```heather
fn CReal::lim(xs: Nat → CReal, h: CReal::Regular(xs)) → CReal {
    CReal(λ n => xs(n + n + 1).seq(n + n + 1), λ m n => CReal::lim_regular(xs, h, m, n))
}
```

The limit's n-th term is the (2n+1)-th term of the (2n+1)-th real. Index
2n+1 makes room for two halves, as at `+`: the real is within 1/(2n+2) of
the limit and its term is within 1/(2n+2) of the real.

Every proof is an estimate on terms, and two bridges cross between real
bounds and term bounds:

- **Real to terms: `dist_terms`.** A bound `(x - y).abs() <= ofRat(r)` read
  at index i says the terms at 2i+1 are within r + 2/(i+1). This is
  `bishop_of_le` (round 3) and nothing more, since `-` and `abs` read the
  same index i of their arguments at 2i+1.
- **Terms to real: `le_of_close`.** x ≤ y when, for every j, x's terms are
  eventually below y's plus 1/(j+1). It is the eventual counterpart of
  `le_of_bishop`, and it is the one these proofs need. Bishop's pointwise
  form allows exactly 2/(i+1) of slack, and `dist_terms` alone already
  spends that, so no diagonal estimate fits under it. The eventual form
  allows any slack that shrinks.

`lim_regular` passes from one diagonal term to the other through both reals'
terms at a far index p = 2i+1. That takes two regularity steps inside the
reals and one `dist_terms` step across. The main parts add up to
1/(m+1) + 1/(n+1), and the slack is at most four 1/(i+1), below any 1/(j+1)
once i = 4j+3. `Rat::le_of_le_add_inv_succ` removes it.
`lim_converges` is the same estimate with one real fixed, through
`le_of_close`.

Two small rational lemmas keep the bookkeeping linear. `add_add_add_comm3`
regroups three "main + slack" bounds into main parts and slack in two
`add_add_add_comm` steps, so no `ring`. `quarters_le` bounds four slack
steps by two halvings.

## Uniqueness, and limits of rationals

- **`limit_unique`**: two limits of one sequence are `≈`. Each direction
  (`limit_le`) refutes a gap: had z been below y by 1/(k+1), a real far out
  would have terms within 3/(i+1) of both limits' terms, and twice that is
  under the gap. Neither limit's regularity is used, only the two
  convergence bounds and the gap.
- **`limit_respects`**: `Limit` respects `≈` in the sequence (pointwise) and
  in the limit. With uniqueness this gives **`lim_respects`**: `≈`
  sequences have `≈` diagonal limits, so `lim` is a function on the setoid
  even though it reads one representation.
- **The reals are the limits of rationals**: a real's embedded terms form a
  regular sequence (`terms_regular`) converging to it (`terms_converge`,
  regularity alone), so `lim_terms` says x ≈ the limit of its own
  approximations. Constant sequences are regular and converge to their value
  (`regular_const`, `limit_const`).

## Computation and probes

`complete` is a theorem whose statement carries data, so its witness opens
to `lim` (`complete_witness`, by `refl` at an open sequence), and a limit's
term evaluates (`lim_term` at a literal). The negative controls: the
naturals embedded are not a regular sequence, by evaluation at (0, 3), and
the zero sequence does not converge to 1, by uniqueness.

## Assumption inventory

Unchanged: none. The limit is a function of the sequence, and the
regularity proof is only carried. The usual construction for general Cauchy
sequences uses countable choice to pick a modulus for each real in the
sequence. Here every real's rate is part of its type, so there is nothing to
choose. The only decisions are still the rationals' order on single terms,
and this round takes none.

## Cost

The construction's proofs are each a single chain of rational estimates.
Their cost is of the same shape as `lt_respects` and `bishop_of_le`, which
are dominated by the kernel gate and elaboration of the `calc` steps. One
repeat of the round-1 finding: in `limit_le`, two `omega` calls (a Nat step
`i ≤ 2i+1` and the strict `1/(2k+2) < 1/(k+1)`) were most of the
declaration's time, because `omega` reflects every rational fact in scope.
They became `Nat::le_add_l` and a new `Rat::inv_succ_half_lt`, proved by
`omega` with nothing in scope, and `le_of_close` uses the same lemma.

## Next

- [real-completeness-interfaces](../../issues/real-completeness-interfaces.md):
  `CReal` is now a carrier that inhabits regular-sequence completeness with
  an explicit rate. A capability class would take its statement from here,
  with `Rat` as the carrier expected not to inhabit it.
- Series and the arithmetic of limits (sums, products of convergent
  sequences) are analysis API, not part of this probe;
  [real-functions-and-derivatives](../../issues/real-functions-and-derivatives.md)
  is where they would be asked for.
