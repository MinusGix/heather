# Regular Cauchy reals: products against the order

Date: 2026-10-18. Continues [creal-order-round](creal-order-round.md) and
[creal-inverse-round](creal-inverse-round.md) in
[`lib/std/creal.hthr`](../lib/std/creal.hthr), with three rational facts
added to [`lib/std/rat.hthr`](../lib/std/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`. It closes
[creal-mul-order](../issues/creal-mul-order.md).

```heather
theorem CReal::mul_pos({x, y: CReal}, hx: CReal::zero() < x, hy: CReal::zero() < y): CReal::zero() < x * y
theorem CReal::mul_nonneg({x, y: CReal}, hx: CReal::zero() <= x, hy: CReal::zero() <= y): CReal::zero() <= x * y
theorem CReal::mul_le_mono_r({x, y, z: CReal}, h: x <= y, hz: CReal::zero() <= z): x * z <= y * z
theorem CReal::mul_lt_mono_r({x, y, z: CReal}, h: x < y, hz: CReal::zero() < z): x * z < y * z
```

with `_l` forms through `mul_comm`.

## A positive product is termwise

The issue planned to read both factors past the later gap start and finish
with `lt_of_term`. That is not needed. A product reads both factors at one
index, `mul_at(n)`, which is at or past n. So from the later of the two
starts on, each factor's term is at least its gap, and the term of the
product is at least 1/(k+1) · 1/(l+1) at every index, not at one.
`Rat::inv_succ_mul` names that product as the step 1/(k(l+1) + l + 1), so the
product's gap is data: the product of the gaps, from the later start. The
gap computes, and the client checks that 0 < 1 (gap 1/2) gives 1 · 1 the
gap 1/4.

## A nonnegative product goes through Bishop's form

`≤` is the refutation of `>`, so `mul_nonneg` refutes a gap 1/(j+1) of x·y
below zero. Bishop's form of 0 ≤ x (`bishop_of_le`) gives x_a ≥ −2/(a+1) at
every index a, with no start. At the index a = (l+1)(2n+2) − 1 the product
reads, both factors are at most l+1 in size, so
`Rat::mul_nonneg_approx` puts their product at least −(l+1) · 2/(a+1). That
is −1/(n+1) exactly (`scale_inv_succ_half`, the same arithmetic as
`mul_regular`). Taking n past both the gap's start and j leaves a gap of
1/(j+1) under a shortfall of 1/(n+1) < 1/(j+1), which the rationals refuse.

`Rat::mul_nonneg_approx` is the one sign-casing step: two rationals each at
least −e and at most m in size have a product at least −m·e. If one of
them is nonnegative, the product loses at most e times its size; if both are
negative, the product is positive.

## The monotone forms are algebra

With the two signs in hand, `mul_le_mono_r` is the sign of the difference:
0 ≤ y − x (`sub_nonneg`), so 0 ≤ (y − x) · z, and
x · z ≈ 0 + x · z ≤ (y − x) · z + x · z ≈ ((y − x) + x) · z ≈ y · z.
The strict form uses `sub_pos` and `mul_pos` in the same chain. The round adds
the small additive facts the chain needed (`zero_add`, `sub_add_cancel`, and
right distributivity `add_mul_distr`).

## What is left

Nothing in the issue's scope. Products with the inverse, such as
0 < x ⇒ 0 < x⁻¹ and dividing an inequality by a positive real, need the
inverse's sign. That landed later, generically over the ordered-field
interface ([ordered-field-inverse-sign](../issues/ordered-field-inverse-sign.md);
`OrderedField::recip_pos` (then `inv_pos`) and its neighbours, at `CReal` through
`CReal::pos_of_mul_pos`).
