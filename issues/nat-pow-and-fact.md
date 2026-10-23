---
title: "Nat: pow and fact, with the laws that are mul's kit one level up"
status: closed
labels: [stdlib,proofs,arithmetic]
created: 2026-08-17
updated: 2026-08-17
---

The half of [[std-api-waves]] wave 3 that needs nothing new from the language,
split from the half that does ([[nat-parity-and-half]], blocked on
[[recursion-at-deeper-subterms]]) so that neither waits on the other.
[[nat-arithmetic-kit]] deliberately did not own these — its charter was
`min`/`max`, the `sub` kit and the order-interaction lemmas, and it said so on
closing.

- **`pow`**, recursing on the exponent with the recursive result on the left of
  the `mul`, which is the shape `mul` already takes to `add`: it keeps
  `pow(a, 0)` definitional.
- **`fact`**, which recurses on its own argument and is the shortest definition
  in the file.
- The laws: `pow_zero`, `pow_one`, `one_pow`, `pow_add`, `pow_mul`, `mul_pow`
  and the `mul_shuffle` rearrangement the last of those needs.
- The order facts, one each: `one_le_pow` under `1 <= a`, and `one_le_fact`
  with `fact_le_succ` beside it.

## What it assumes from elsewhere

- **[[nat-arithmetic-kit]]** (closed) owns `mul_le_mono`. Assumed here: only
  that it exists and is stated at open arguments, which is what makes
  `one_le_pow` and `one_le_fact` one line each instead of an induction with
  arithmetic in it.
- **[[std-api-waves]]** owns sequencing. Assumed here: nothing.

## Acceptance

The names above exist in `lib/std/num/nat.hthr` with proofs, `pow(2, 5) = 32` and
`fact(5) = 120` are `refl`, and the laws are exercised at **open** arguments
with negative controls that they are not definitional there.

## Log

- 2026-08-17: LANDED, in one pass. `lib/std/num/nat.hthr` gained a closing section: `pow`, `fact`,
seven laws and three order facts.

`pow` recurses on the exponent and puts the recursive result on the LEFT of the
`mul` — the shape `mul` already takes to `add`, and for the same payoff:
`pow(a, 0)` is `1` definitionally, so `pow_zero` is `refl` even at open `a`.
The endpoint one step along is NOT definitional and the asymmetry is worth
recording, because it is where a reader's expectation breaks: `pow(a, 1)` is
`mul(1, a)`, which descends on `a`, so it costs `mul_left_one`. Test pinned in
both directions.

The laws are `mul`'s kit read one level up, and the resemblance is structural
rather than poetic: `pow_add` is to `mul_assoc` what `mul_add_distr` is to
`add_assoc`, and `pow_mul` is not a second induction at all but `pow_add`'s
first customer (`mul(b, Succ k)` is `add(mul(b, k), b)`). `mul_pow` needed the
middle-exchange rearrangement, which is factored out as `mul_shuffle` — it is
about `mul` alone, and a reader looking for it should not have to find it
inside a `pow` proof.

The two order facts are the payoff from [[nat-arithmetic-kit]] landing first:
`one_le_pow` and `one_le_fact` are both `mul_le_mono` applied to the IH and the
hypothesis, one line each, where without the monotonicity kit each would have
been an induction with arithmetic in it. `mul(1, 1)` is `1` by computation, so
neither conclusion needs repackaging. `fact_le_succ` is the same trick with the
transport `mul_left_one` supplies.

**One conversion fact learned by being wrong about it.** `pow(a, 1) = a` checks
with `add_left_zero(a)` *and* with `mul_left_one(a)`, which looked like an
anomaly: `mul(1, a)` and `add(0, a)` are both stuck at open `a`. They are not
two stuck terms — both are `ElimNat` on `a`, their bases are `Zero`, and their
steps are `add(ih, 1)` and `Succ(ih)`, which are definitionally equal. The
kernel compares eliminators componentwise and converts them. Reasoning about
"stuckness" at the surface is not a substitute for that. `mul_left_one` is the
idiomatic proof and is what landed.

**Tests**: `crates/elab/tests/nat_arith.rs` §5, six tests, three of them
negative controls — the wrong closed values, the three laws attempted by `refl`
at open arguments (which is what makes the positive law tests non-vacuous), and
`one_le_pow` without its hypothesis, with `pow(0, 3) = 0` beside it as the
counterexample that says why the hypothesis exists.

Not here: `pow` notation (`^`), which is [[bool-operator-designations]]'s kind
of question and not this issue's, and `n <= fact(n)`, which is true and wants
an induction with a real inequality step — filed nowhere, mentioned here so the
next person knows it was considered rather than missed.
