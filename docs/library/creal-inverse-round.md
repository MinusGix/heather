# Regular Cauchy reals, third round: the inverse

Date: 2026-10-17. Continues [creal-multiplication-round](creal-multiplication-round.md)
in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr), with the rational estimates
it needs added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round defines the inverse of a real apart from zero, with
`inv_respects`, `mul_inv` and `inv_mul` modulo `≈`
([creal-inverse](../../issues/creal-inverse.md)).

## The gap

Apartness from zero is `x < 0 ∨ 0 < x`, and either side is a gap given as
data: a k and a start index from which the terms clear zero by 1/(k+1).
`away_of_apart` forgets the side and keeps the size:

```heather
fn CReal::Away(x: CReal, k, start: Nat) → Type {
    (n: Nat) → start <= n → Rat::inv_succ(k) <= x.seq(n).abs()
}

theorem CReal::away_of_apart(self x: CReal, h: x.Apart(CReal::zero())): ∃ k: Nat, ∃ start: Nat, x.Away(k, start)
```

The sign is not needed, because every estimate below bounds a reciprocal by
the size of what it inverts.

## Where the inverse reads

Past the gap's start, the reciprocal is Lipschitz with constant (k+1)²:
1/a - 1/b = (1/a)(1/b)(b - a), and each reciprocal is at most k+1 in size
(`Rat::inv_abs_le`). So the inverse reads x at an index where x's own rate
is (k+1)² times finer than the inverse's:

```heather
fn CReal::inv_at(k, start, n: Nat) → Nat { start.max((k + 1) * (k + 1) * (n + 1) + n) }

fn CReal::inv_gap(self x: CReal, k, start: Nat, gap: x.Away(k, start)) → CReal {
    CReal(λ n => x.seq(CReal::inv_at(k, start, n)).inv(), λ m n => x.inv_regular(k, start, gap, m, n))
}
```

The index is (k+1)²(n+1) - 1 + 1, written as m(n+1) + n with m = (k+1)², so
it needs no subtraction. The issue suggested (k+1)²(2n+2) - 1. The factor 2
is not needed: the inverse's regularity is one reciprocal estimate per index,
and each index pays for its own (k+1)², so no halving is involved
(`inv_regular`). `Rat::scale_inv_succ_le` does that payment. It is
`scale_inv_succ` with one unit of slack, so that the factor need not be
written as a successor: m · e ≤ 1/(n+1) whenever e ≤ 1/(j+1) and
j ≥ m(n+1) + n.

`CReal::inv(x, h)` is `inv_gap` at the gap `away_of_apart(h)` carries, read
through `.witness` and `.proof`.

## The laws, for any gap

Every law is proved for `inv_gap` at an arbitrary gap first, so two proofs of
apartness that carry different gaps still give `≈` inverses:

- **`inv_gap_respects`**: x ≈ x2 with gaps (k, s) and (l, t). The two
  reciprocals are within (k+1)(l+1) times the distance of the terms they
  invert (`Rat::dist_inv_le` with two gaps). Those terms sit at different
  indices, wherever the two gaps put them, so `same_close_far` bounds their
  distance by 1/((k+1)(l+1)(K+1)).
- **`mul_inv_gap`**: x · x⁻¹ reads x at a = `mul_at(n)` and the inverse at a,
  which reads x at b further out. The rational x_b · x_b⁻¹ is exactly 1
  (`Rat::mul_inv`, nonzero by the gap), so
  x_a · x_b⁻¹ - 1 ≈ x_b⁻¹ · (x_a - x_b). That is at most (k+1) times a
  regularity distance, and `regular_close` makes it small from index
  2j+1 on, where j = (k+1)(K+1) + K.

At an apartness proof these become `inv_respects` (the two proofs may differ),
`mul_inv`, `inv_mul` by commutativity, and `ofRat_inv`, which is termwise
because a constant sequence reads the same wherever the gap sends it.

## The rational estimates

All in `rat.hthr`, beside the other distance facts:

- `nonzero_of_gap`: |a| ≥ 1/(k+1) gives a ≉ 0.
- `inv_abs_le`: |a| ≥ 1/(k+1) gives |a⁻¹| ≤ k+1. A larger reciprocal would
  make |a · a⁻¹| = 1 larger than (1/(k+1))(k+1) = 1. The proof is a
  refutation of `<`, decided by the integer order. It needs no case split on
  the numerator's sign.
- `sub_of_inverses` and `mul_sub_one_of_inverse`: the two rearrangements, by
  `mul_inv` hypotheses and one `ring` call each.
- `dist_inv_le`: |a⁻¹ - b⁻¹| ≤ (k+1)(l+1)|a - b|.
- `le_abs_of_add_le_zero` and `le_abs_of_zero_add_le`: a gap below zero or
  above it is a lower bound on the size.

## Computation

The gap is read from the apartness proof's sealed proofs
([theorem-witness-unfolding](../../issues/theorem-witness-unfolding.md)), so the
inverse evaluates. At 0 < 1, `CReal::ofRat_lt` finds k = 1 through
`Rat::archimedean_inv`, the test checks `away_of_apart`'s witness is 1 and
refuses 0, and term 3 of 1⁻¹ is `Rat::one()` by `refl`. The reciprocal of
-2 reads -1/2, and the showcase evaluates term 4 of 2⁻¹ to 1/2.

## Refusals at zero

Zero has no inverse because no gap above or below it can be built. The test
refuses a hand-claimed gap 0 + 1 ≤ 0, while the same claim at 1 is accepted.
It also refuses an inverse asked for without a proof, and it proves that an
apartness proof at zero is absurd. The inverse is not the termwise
reciprocal, and that equation is refused by `refl` too. A wrong field law,
x · x⁻¹ ≈ 0, is refused as well.

## Assumption inventory

Nothing new: no choice, no excluded middle, no function extensionality, no
proof irrelevance. `inv_abs_le` refutes a strict inequality between
rationals, and the rationals' order decides.

## Cost

Each law is one estimate plus Nat bookkeeping, as for products. The start
indices again chain `le_trans`, `le_max_l/r` and `le_add_r`, never `omega`.
The two `ring` identities each take their denominators as hints, in the
pattern of `Rat::mul_sub_mul`, and they went through in one call.

## Next

- **The Bishop bridge and monotonicity**
  ([creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md)).
  With it, `0 < x → 0 < x⁻¹` and the order's interaction with the inverse
  become statable. They are left out here.
- The diagonal completeness construction, after the bridge.
