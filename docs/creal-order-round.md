# Regular Cauchy reals, third round: Bishop's forms and order with addition

Date: 2026-10-17. Continues [creal-multiplication-round](creal-multiplication-round.md)
in [`lib/std/creal.hthr`](../lib/std/creal.hthr), with two rational facts
added to [`lib/std/rat.hthr`](../lib/std/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`. It closes
[creal-order-and-bishop-bridge](../issues/creal-order-and-bishop-bridge.md).

## Bishop's equality

Bishop calls two regular sequences equal when their n-th terms are within
2/(n+1) at every n. That is a bound at each index with no modulus, where
`≈` gives a start index for each 1/(k+1). The round shows they are the
same relation:

```heather
fn CReal::BishopSame(x, y: CReal) → Type {
    (n: Nat) → (x.seq(n) -y.seq(n)).abs() <= Rat::inv_succ(n) + Rat::inv_succ(n)
}

theorem CReal::same_of_bishop({x, y: CReal}, h: x.BishopSame(y)): x ≈ y
theorem CReal::bishop_of_same({x, y: CReal}, h: x ≈ y): x.BishopSame(y)
```

- **Pointwise to eventual** is immediate: from index 2k+1 on, 2/(n+1) is
  at most two halves of 1/(k+1).
- **Eventual to pointwise** compares the n-th terms through a far index m.
  Regularity moves x_n to x_m and y_m to y_n by 1/(n+1) + 1/(m+1) each, and
  `≈` crosses from x_m to y_m. Taking `≈` at 1/(4j+4) and m past both its
  start and 4j+3, the excess over 2/(n+1) is three quarters of 1/(j+1) at
  most. An excess below every 1/(j+1) is nothing:
  `Rat::le_of_le_add_inv_succ` is the one-sided `Rat::same_of_close`, by
  `archimedean_inv` on the would-be excess. The proof is a refutation of a
  rational order, which is decidable, so nothing classical enters.

## Bishop's order

Bishop reads x ≤ y pointwise too, as x_n ≤ y_n + 2/(n+1) at every n
(`CReal::BishopLe`). It agrees with `≤` as the refutation of `>`:

- **`le_of_bishop`**: a gap of 1/(k+1) with y below x, read at an index
  past its start and past 4k+3, puts x_n at least 1/(k+1) above y_n, while
  the pointwise bound keeps it within 2/(n+1) ≤ 1/(2k+2). The rationals
  refuse that.
- **`bishop_of_le`**: if x_n were above y_n + 2/(n+1) by 1/(j+1), then at
  m = 16k + 15 with k = 2j+1 regularity moves each term by under a quarter
  of that, `Rat::le_of_close_gap` leaves y_m + 1/(2k+2) ≤ x_m, and
  `lt_of_term` makes it y < x, which `≤` refutes. So every excess is
  refuted, and `Rat::le_of_le_add_inv_succ` again closes the bound.

The new `Rat::add_left_comm` does the one rearrangement this needed.

## Order and addition

A sum reads both summands at index 2n+1, so adding z to both sides of
x < y adds the same rational to both terms there. `add_lt_mono_r` is
therefore termwise: the sums' gap is x's gap, the same 1/(k+1) from the
same start, and it computes (the showcase evaluates it). The rest follows
from it without reading terms again:

- `add_lt_mono_l` by commutativity, and `add_lt_mono` by transitivity.
- `add_lt_cancel_r` and `add_lt_cancel_l` add -z back
  (`add_neg_cancel_r`, (x + y) + -y ≈ x).
- `add_le_mono_r/l` are cancellation under the refutation, and
  `add_le_mono`, `add_lt_le_mono` and `add_le_lt_mono` chain them.
- `add_lt_cancel` is Bishop's splitting. A gap between x + y and x2 + y2
  lies between x and x2 or between y and y2: cotransitivity places x2 + y
  against the gap, and each side cancels.

The signs of a sum are corollaries: `add_pos`, `add_nonneg` and
`add_pos_of_nonneg_of_pos`, and conversely `pos_of_add_pos`. A positive
sum names one positive summand, as data, by the splitting above.

## Assumption inventory

Nothing new. Every proof into `≤` is a refutation, and the two rational
facts use only the decidable rational order and `archimedean_inv`.

## Cost

Each law here is a few `calc` steps over existing estimates. The dearest is
`bishop_of_le`, which rearranges one sum of six rational terms through
`Rat::add_left_comm` and `Rat::add_add_add_comm` rather than one `ring` call.
Start indices again chain `Nat` lemmas; `omega` appears only on facts with
no `Rat` hypothesis in scope that it would have to unfold.

## Next

- **Products against the order**
  ([creal-mul-order](../issues/creal-mul-order.md)): `mul_pos` and
  `mul_le_mono` for nonnegative factors. A product's gap needs a lower
  bound on each factor past its gap's start, which the canonical bound
  does not give, so it is not termwise like a sum's.
- **The inverse** ([creal-inverse](../issues/creal-inverse.md)), in its own
  round.
- **Completeness**: the diagonal limit of a regular sequence of reals.
  Bishop's pointwise forms are the natural statements for its estimates.
