# Regular Cauchy reals, second round: products and `≤`

Date: 2026-10-17. Continues [regular-cauchy-reals-round](regular-cauchy-reals-round.md)
in [`lib/std/num/creal.hthr`](../lib/std/num/creal.hthr), with the rational estimates
it needs added to [`lib/std/num/rat.hthr`](../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round adds multiplication with its laws modulo `≈`
([creal-multiplication](../issues/creal-multiplication.md)), and the
non-strict order `≤` as the refutation of `>`, the first half of
[creal-order-and-bishop-bridge](../issues/creal-order-and-bishop-bridge.md).
The inverse is left to its own round ([creal-inverse](../issues/creal-inverse.md)).

## The canonical bound

A product's error is each factor's error weighted by the other factor's
size, so to stay inside the fixed rate a product must know how large its
factors are. Every real carries such a bound for free:

```heather
fn CReal::bound(self x: CReal) → Nat { x.seq(0).num.natAbs() + 2 }
```

Every term is within 1/(n+1) + 1 ≤ 2 of x_0 (regularity at n and 0), and
|x_0| = |a|/p is at most |a| because p ≥ 1 (`Rat::abs_le_natAbs`). So
`bound_le` gives |x_n| ≤ bound(x) for every n. It is a `Nat`, so it can
index a sequence, and it computes: the bound of the constant -7/2 is 9.

The bound is a function of the representation, not of the real. Two `≈`
reals can have different bounds, so the product of `≈` factors reads them at
different indices. That one fact decides how every proof below is shaped.

## The product

```heather
fn CReal::mul_at(self x, y: CReal, n: Nat) → Nat { x.bound().max(y.bound()) * (n + n + 1 + 1) + (n + n + 1) }

fn CReal::mul(self x, y: CReal) → CReal {
    CReal(λ n => x.seq(x.mul_at(y, n)) * y.seq(x.mul_at(y, n)), λ m n => x.mul_regular(y, m, n))
}
```

With l the larger bound, `mul_at(n)` is (l+1)(2n+2) - 1. Each factor's
error there is 1/((l+1)(2n+2)), the other factor scales it by at most l+1,
and what remains is 1/(2n+2) per factor, so the two add to 1/(n+1). The
rational identity behind the scaling is `Rat::scale_inv_succ`:
(l+1) · 1/((l+1)(k+1)) ≈ 1/(k+1). The index is written without subtraction,
as l(k+1) + k, so it needs no side condition.

The product estimate itself is a rational lemma, `Rat::dist_mul_le`: with
|a|, |d| ≤ m and |b - d|, |a - c| ≤ e, |ab - cd| ≤ me + me, from
ab - cd = a(b - d) + d(a - c). Regularity of the product is that lemma with
the bound and the two factors' regularity.

## One estimate for every law

`mul_close` is the lemma all the product laws go through:

```heather
theorem CReal::mul_close({x, x2, y, y2: CReal}, hx: x ≈ x2, hy: y ≈ y2, k: Nat):
    ∃ start: Nat, (a, b, c, d: Nat) → start <= a → start <= b → start <= c → start <= d →
        (x.seq(a) * y.seq(b) -x2.seq(c) * y2.seq(d)).abs() <= Rat::inv_succ(k)
```

Its four indices are independent. Taking them that way is what makes one
lemma enough, because the two sides of almost every law read their factors
at different depths. It rests on `same_close_far`: `x ≈ x2` read at two far
indices a and b, within 1/(2k+2) along x by regularity and then within
1/(2k+2) across to x2 at b.

- **`mul_respects`** is `mul_close` at the indices the two products read. It
  backs a `Respects2` instance, so `rel_cong` works through `*`.
- **`mul_comm`** is not termwise, perhaps surprisingly.
  `x.bound().max(y.bound())` and `y.bound().max(x.bound())` are the same
  number but not the same term, so x · y and y · x read different indices.
  It is `mul_close` with reflexivity, after commuting the rational product.
- **`mul_assoc`** reads z at one index and x, y further out on the left, and
  x at one index and y, z further out on the right. Reassociating the
  rational product makes both sides an x term times a y·z term, so
  `Rat::dist_mul_le` applies once more, with the y·z terms bounded by the
  product of the bounds and their distance given by `mul_close` on y and z.
- **`mul_add_distr`** distributes the rational product and then bounds each
  pair of products by `mul_close`.
- **`mul_one`** compares x at a far index with x at n, which is
  `regular_close`.
- **`mul_zero`** and **`ofRat_mul`** are termwise.

`CReal` registers `Semigroup` and `Commutative` for `*` modulo `≈`.

## `≤` is the refutation of `>`

```heather
fn CReal::Le(x, y: CReal) → Type { ¬(y < x) }
```

This is Bishop's order. It carries no data and is defined from `<`, never
the reverse, as the first round's ordered-field notes asked. Every law is
one use of cotransitivity, which places a third real against a gap:

- `le_trans`: z < x places y, so z < y or y < x, and each is refuted.
- `lt_of_lt_of_le` and `lt_of_le_of_lt` keep the side of the gap that is
  not refuted.
- `le_antisymm` is tightness. Reals each below the other are not apart, so
  they are `≈`.
- `le_of_lt`, `le_of_same`, `le_respects`, and the embedding preserving and
  reflecting `≤` (`ofRat_le`, `le_of_ofRat_le`).

`CReal` registers `Preorder` for `≤` and the four mixed `Trans` pairs, so a
`calc` chain may mix `≈`, `≤` and `<`. The showcase chains all three.

## Computation

The data-carrying lemmas of this round are theorems: `same_close_far` and
`mul_close` carry start indices, and the laws carry them through. This is the
first round that opens sealed proofs in a chain
([theorem-witness-unfolding](../issues/theorem-witness-unfolding.md)). The
modulus of `mul_comm` at 1 · 1 opens `mul_comm`, then `mul_close`, then two
uses of `same_close_far`, then `same_refl`, and evaluates to 55 by `refl`.
The arithmetic: both bounds are 3, so the factors must agree within
1/((6+1)·2) = 1/14. `same_close_far` asks for halves of that, 1/28, which
regularity grants from index 2·27+1 = 55. The test refuses 54.

A product's terms compute too. The showcase evaluates the first term of
1/2 · 1/3, which reads both constants at index 5.

## Assumption inventory

Nothing new: no choice, no excluded middle, no function extensionality, no
proof irrelevance. `≤` is a negation, and every use of it is a refutation.
Nothing here needs it eliminated classically.

## Cost

Each product law is one `mul_close` instance plus Nat bookkeeping, so the
dearest declarations are `mul_assoc` and `mul_add_distr`, which carry four
far indices each. The start-index arithmetic chains `Nat::le_trans`,
`le_max_l/r`, `le_add_l/r` and `le_succ_r`, never `omega`, for the reason the
first round recorded: `omega` pays for every `Rat` fact in scope. The one
nonlinear identity, `Rat::scale_inv_succ`, needed `ring` in three steps. One
call with all its hints failed to find the combination, so the
denominator of the product is computed first and then related to the target.

## Next

- **The inverse** ([creal-inverse](../issues/creal-inverse.md)): a real apart
  from zero has a gap 1/(k+1) from some index on, so its terms are at least
  that far from zero, and 1/x reads index (k+1)²(n+1) - 1 past the gap's
  start. `mul_inv` then compares x_a / x_c with 1 across indices, which is
  `same_close_far` again.
- **The Bishop bridge and monotonicity**
  ([creal-order-and-bishop-bridge](../issues/creal-order-and-bishop-bridge.md)):
  `≈` against pointwise closeness, and `+` and `*` against `<` and `≤`.
