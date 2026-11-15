# The rationals' order, completed

Date: 2026-10-14. Follows [setoid-rationals-round](../showcase/setoid-rationals-round.md),
which left `Rat` with `≤`, its preorder laws modulo `≈`, right addition
monotonicity and non-negative products. This round adds what the
real-number probes ([regular-cauchy-reals](../../issues/regular-cauchy-reals.md))
reach for first, in [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr):

- strict `<`, its agreement with `¬ ≤`, mixed transitivity, trichotomy,
  cotransitivity and tightness;
- negation and addition against both orders, binary `-`;
- `abs`, the triangle inequality, `|x - y|` as a distance;
- scaling by a non-negative (`≤`) or positive (`<`) factor, `mul_pos`;
- the Archimedean property in both directions, and `inv_succ(n)` = 1/(n+1)
  with the bounds a Cauchy modulus uses.

`docs/showcase/rat_client.hthr` gains the estimate a regular Cauchy sequence
chains (two points within 1/(2n+2) of a third are within 1/(n+1) of each
other), and `crates/elab/tests/lib_std_rat.rs` names the new laws and adds
negative controls for each side condition.

## Strict order: the positive-difference form

```heather
fn Rat::Lt(x, y: Rat) → Type { x.num * y.den.int() < y.num * x.den.int() }
```

The issue asked to choose between `¬(y ≤ x)` and a positive-difference form
with [apartness](../../issues/apartness-structures.md) in mind. The
cross-multiplied `<` of `Int` is the positive form: it is a proposition with
content (the integer gap), omega reads it as it stands, and it is what a
constructive real's `<` is built from (a rational lower bound on a positive
difference). `¬ ≤` is the derived view, not the definition. The two agree at
`Rat` because the integer order decides; `lt_of_not_le` and `not_le_of_lt`
are one `omega` each.

That agreement is also how the order-theoretic laws avoid arithmetic.
`lt_respects`, `lt_of_lt_of_le`, `lt_of_le_of_lt` and `add_lt_mono_r` are
proved by turning a counterexample to the conclusion into a `≤` chain that
contradicts the strict premise, so they reuse the `≤` laws instead of
re-deriving cross-multiplication facts.

Cotransitivity (`x < y → x < z ∨ z < y`) is the law a constructive real keeps
in place of trichotomy, so it is stated here even though `Rat` also has
`lt_trichotomy`. Its proof decides `z ≤ x` with the new `Rat::le_dec`, which
also backs an `instance Decide<Rat::Le(x, y)>` (an `if x <= y` at `Rat`).
Tightness is `same_of_not_lt`.

`Rat` registers `Preorder` and `Total` for `≤` and `Irreflexive` and
`Transitive` for `<`. It cannot register `PartialOrder`: `Antisymmetric` is
stated with `=`, and `Rat`'s antisymmetry only holds modulo `≈`. An
ordered-field instance waits for
[constructive-ordered-field-interface](../../issues/constructive-ordered-field-interface.md)
to define the interface.

## Absolute value

`Rat::abs(x)` is `Rat(x.num.abs(), x.den)`: the numerator's absolute value
over the same denominator. Multiplicativity and `|-x| ≈ |x|` then cross
`same_of_parts` with an `Int` fact about `natAbs`, and `abs_respects`
moves `|·|` through the cross-multiplication with `Int::abs_mul` (the
denominator is its own absolute value).

The rest is setoid reasoning, not arithmetic. `Rat::abs_cases` splits on the
numerator's sign (`0 ≤ x ∧ |x| ≈ x`, or `x < 0 ∧ |x| ≈ -x`), `abs_le`
derives `|x| ≤ y` from `-y ≤ x ≤ y`, and the triangle inequality is
`abs_le` over two `add_le_mono`s. Distance symmetry and `dist_triangle` are
`calc` chains over `≈` with `rel_cong`.

The `Int` facts this needed (`abs_cases`, `le_abs`, `neg_le_abs`,
`abs_of_nonneg`, `natAbs_mul`, `abs_mul`, `abs_neg`, `mul_lt_mono_r`) live in
`rat.hthr` beside their only client, the way `pos.hthr` keeps the
cancellation lemmas. Moving them into `int.hthr` re-elaborates everything
downstream of `int`; they move when a second client wants them.

## Products: `ring` for the equations, `omega` for the order

`mul_le_mono_r(x, y, z, h, hz)` is the template. With `x = a/p`, `y = c/q`,
`z = e/r`, the goal is `(a·e)·(q·r) ≤ (c·e)·(p·r)` once the product
denominators are read as products (`Pos::mul_int`). The proof:

1. scales the premise `a·q ≤ c·p` by `e·r ≥ 0` (`Int::mul_le_mono_r`);
2. states each side of the goal as the scaled premise's side, one
   `let … = ring(den.mul_int(…))` each;
3. lets `omega` join them with every product as an atom.

This is the shape [ring-inequalities](../../issues/ring-inequalities.md) would
automate; until then it is three lines per law and no monomial matching by
hand. The strict version swaps in the new `Int::mul_lt_mono_r`.

## Archimedean facts

`Rat::archimedean(x)` gives `n` with `x < n` (the witness is `|num| + 1`,
because the denominator is at least one). `Rat::archimedean_inv(ε, 0 < ε)`
gives `n` with `1/(n+1) < ε` (the witness is `ε`'s denominator value: with
`ε = e/r` and `e ≥ 1`, `r < e·(r+1)`). Both are explicit `Exists`
witnesses. They are `theorem`s whose statements carry data, so a client
that projects the witness computes it
([theorem-witness-unfolding](../../issues/theorem-witness-unfolding.md)).
Before that landed a `theorem` was opaque and the claim held only of the
source; [regular-cauchy-reals-round](regular-cauchy-reals-round.md) made
them `fn`s for a while.

`inv_succ(n)` has its denominator positive by construction (`Pos(n)`), so its
laws (`inv_succ_pos`, `inv_succ_le_one`, `inv_succ_antitone`, and
`inv_succ_half`: 1/(2n+2) + 1/(2n+2) ≈ 1/(n+1)) carry no side condition.

## What the round exposed

1. **No `calc` over `≤`/`<`** ([calc-over-order-relations](../../issues/calc-over-order-relations.md)).
   The showcase's `two_halves_close` is a three-step inequality chain written
   as nested `le_trans`/`le_respects` calls. This is the trigger that issue
   was waiting for.
2. **omega stops at a projection of a projection of a call**
   ([omega-nested-projection-of-call](../../issues/omega-nested-projection-of-call.md)).
   `Pos(n).int()` reads, `Rat::inv_succ(n).den.int()` does not; the round
   restated two denominators with `refl`.
3. **Binary `-` is formatted tight** ([infix-subtraction-notation](../../issues/infix-subtraction-notation.md)).
   `Rat` now designates binary `-`, so the distance laws are checked in as
   `(x -y).abs()`; they read correctly once the formatter is fixed.
