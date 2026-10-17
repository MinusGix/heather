# Regular Cauchy reals, first round

Date: 2026-10-16. Starts [regular-cauchy-reals](../issues/regular-cauchy-reals.md)
on top of the completed rational order ([rational-order-round](rational-order-round.md))
and `calc` over order relations ([calc-order-chains](calc-order-chains.md)).
New module [`lib/std/creal.hthr`](../lib/std/creal.hthr); the rational facts
it chains are added to [`lib/std/rat.hthr`](../lib/std/rat.hthr); the client
is [`docs/showcase/creal_client.hthr`](showcase/creal_client.hthr); the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round covers the representation, the rational embedding, `≈` as a
setoid, negation and addition with their laws, and the strict order with
apartness. Multiplication and completeness come next (the last section).

## The representation

```heather
record CReal {
    seq: Nat → Rat,
    regular: (m, n: Nat) → (seq(m) -seq(n)).abs() <= Rat::inv_succ(m) + Rat::inv_succ(n),
}
```

These are Bishop's regular sequences, indexed from zero: the n-th term is
within 1/(n+1) of the number, so two terms are within the sum of their
rates. The rate is fixed and part of the type, so no real carries a modulus
of its own and arithmetic needs no modulus bookkeeping: an operation reads
its arguments far enough out to stay inside the rate. `Rat::inv_succ(n)`
from the order round is the rate, and `Rat::inv_succ_half` (two halves of
1/(n+1) are 1/(2n+2) each) is the one identity nearly every estimate ends on.

The name is `CReal` and not `Real` because this is one presentation among
those [real-number-foundation](../issues/real-number-foundation.md) compares.

## Equality: eventually close, with the modulus as data

```heather
fn CReal::Same(x, y: CReal) → Type {
    (k: Nat) → ∃ start: Nat, (n: Nat) → start <= n → (x.seq(n) -y.seq(n)).abs() <= Rat::inv_succ(k)
}
```

Bishop's own definition is pointwise, `|x_n - y_n| ≤ 2/(n+1)` for every
n. Its transitivity needs his Lemma 2.3 (the eventual form) to go through,
whereas with the eventual form transitivity is one triangle inequality:
match both hypotheses at 2k+1, start from the later index, and the two
halves add to 1/(k+1). The pointwise form implies this one directly (from
index 2k+1 on, 2/(n+1) ≤ 1/(k+1)). The converse is the Bishop bridge, owned
by the next round (below).

`∃` is a record (`Exists`), so the start index is data a client can compute
with, not a proof of existence. Two laws cover nearly every equation:
`same_of_terms` (termwise `≈`, from index 0) and `same_of_close` (closeness
within 1/(k+1) from index 2k+1 on, the shape regularity hands out through
`regular_close`).

`=` is strictly finer than `≈` here, as at `Rat`. Sequences that differ, or
approach the same number at different speeds, are `≈` and not `=`, and the
regularity proofs are never compared.

## The rationals inside

`CReal::ofRat(q)` is the constant sequence. It respects `≈`
(`ofRat_respects`) and reflects it (`ofRat_inj`). Reflection needs the new
`Rat::same_of_close`: rationals within every 1/(k+1) of each other are `≈`,
because a positive distance would sit above some 1/(k+1)
(`Rat::archimedean_inv`). It also commutes with `-` and `+` (`ofRat_neg`,
`ofRat_add`), and preserves and reflects `<` (`ofRat_lt`,
`lt_of_ofRat_lt`).

## Negation and addition

Negation reads the same index. A sum reads index 2n+1 of both summands:

```heather
fn CReal::add(self x, y: CReal) → CReal {
    CReal(λ n => x.seq(n + n + 1) + y.seq(n + n + 1), λ m n => x.add_regular(y, m, n))
}
```

Each summand's two terms are within 1/(2m+2) + 1/(2n+2), and the four
halves regroup into 1/(m+1) + 1/(n+1). The regrouping is
`Rat::add_add_add_comm`, proved by `ring`. `add_respects` and
`neg_respects` back a `Respects2` instance, so `rel_cong` works through `+`
at `CReal` as it does at `Rat`. The showcase cancels `y + -y` inside a sum
with it.

The laws, all modulo `≈`, fall into two kinds:

- **Termwise:** `add_comm` and `add_neg`. Both sides read the same indices,
  so `same_of_terms` with the rational law closes them.
- **Across indices:** `add_zero` compares `x_{2n+1}` with `x_n`, and
  `add_assoc` compares terms at 2n+1 and 4n+3. Regularity bounds each
  difference (`regular_close`), and the bounds add up to 1/(k+1) once
  n ≥ 2k+1.

`CReal` registers `Semigroup` and `Commutative` for `+` modulo `≈`.

## Strict order: an eventual gap

```heather
fn CReal::Lt(x, y: CReal) → Type {
    ∃ k: Nat, ∃ start: Nat, (n: Nat) → start <= n → x.seq(n) + Rat::inv_succ(k) <= y.seq(n)
}
```

`x < y` gives a gap size and the index where it starts, as data. This is the
same positive-difference reading `Rat::Lt` took, and it is never `¬(y ≤ x)`.
The workhorse is `lt_of_term`. A single index n ≥ 16k+15 where y's term
clears x's by 1/(2k+2) is enough, because from there on later terms move by
at most 1/(8k+8) each, so a gap of 1/(4k+4) survives. The rational step
behind it is `Rat::le_of_close_gap`: a gap of q + 2e survives moving each
side by e. `lt_respects` uses the same step, since moving along `≈` costs a
quarter of the gap on each side.

The laws:

- **Irreflexivity and transitivity** (`lt_irrefl`, `lt_trans`) are
  registered as `Irreflexive` and `Transitive`. Mixed `Trans` pairs of `≈`
  with `<` let `calc` chains pass through `≈` steps.
- **Cotransitivity** (`lt_cotrans`) is the law a constructive order keeps in
  place of trichotomy. Far enough out it compares z's term with the midpoint
  of x's and y's using `Rat::le_dec`, and either side of the midpoint leaves
  half the gap for `lt_of_term`.
- **Apartness** (`CReal::Apart`, `x < y ∨ y < x`) is irreflexive, symmetric
  and cotransitive.
- **Tightness** (`same_of_not_apart`) says reals that are not apart are
  `≈`. If neither term were within 1/(2k+2) of the other, `lt_of_term` would
  produce an apartness. That step needs no decision at all; `lt_of_not_le`
  is the integers' order.

## Computation: witnesses of theorems evaluate

A `CReal` declaration whose statement carries data is a `theorem` like any
other proof: the `≈` builders and laws (their start indices), the `<`
builders (gap and start), cotransitivity (which side), apartness symmetry
and cotransitivity, and tightness. Their witnesses still compute. A theorem
whose statement carries data keeps its proof sealed beside its opaque
binding, and a projection or `match` stuck on it opens the proof
([theorem-witness-unfolding](../issues/theorem-witness-unfolding.md)). The
showcase evaluates a sum's term (`sum_term`), a modulus (`add_zero_start`)
and a gap (`one_gap`) by `refl`, and `lib_std_creal.rs` refuses a wrong
modulus by the same evaluation.

The round first wrote these proofs as `fn`s, because a `theorem` was then
opaque. That made the author guess, at definition time, whether anyone
would compute with a proof, and gave up the edit firewall for every one of
them. Now only the declarations that open a proof re-check when it is
edited. The same correction applies to
[rational-order-round](rational-order-round.md): `Rat::archimedean` and
`Rat::archimedean_inv` are theorems again, and `one_gap` shows the witness
flowing through `ofRat_lt`.

## Assumption inventory

None in the core: no excluded middle, no choice, no function
extensionality, no proof irrelevance, no quotient. Concretely:

- **Choice** never enters, because every `∃` is a record whose witness is
  computed. The moduli of `≈` and the gaps of `<` are functions of the
  inputs.
- **Function extensionality** is not needed, because `≈` compares terms and
  never sequences as functions.
- **Proof irrelevance** is not needed, because the regularity field is never
  compared.
- **Decisions:** the only one taken is the rationals' order on single terms
  (`Rat::le_dec` in `lt_cotrans`), which reduces to the integers' order.

## What the ordered-field interface learns from a second carrier

For [constructive-ordered-field-interface](../issues/constructive-ordered-field-interface.md):

1. **Nothing decides at `CReal`.** There is no `le_dec`, no decidable `≈`
   and no trichotomy, so the interface may require none of them. `Rat`
   provides them as extras.
2. **The shared core is setoid plus strict order plus apartness.** Both
   carriers have `≈` as an `Equivalence`, `<` that is irreflexive,
   transitive and respects `≈`, cotransitivity, and tightness in the form
   "not apart implies `≈`". At `Rat` the last is `same_of_not_lt`. At
   `CReal` it is `same_of_not_apart`, and the two coincide once apartness is
   defined as `x < y ∨ y < x`.
3. **`<` is data at both carriers.** The interface should take `<` as
   primitive and derive `≤` as `¬(y < x)` (Bishop's), not the reverse.
   `CReal` has no `≤` yet. When it does, its antisymmetry is tightness, so,
   as at `Rat`, antisymmetry modulo `≈` and not `Antisymmetric` with `=`.
4. **Archimedean in the `inv_succ` form fits both.** `Rat` has it; `CReal`
   needs "0 < x gives some 1/(k+1) below x", which the gap of `<` already
   is: `x < y` contains such a k.
5. **Locatedness is free here.** The issue asked whether locatedness belongs
   in the base interface or in a separate capability. Cotransitivity at
   `CReal` is locatedness (every z is placed relative to any gap), and it
   costs nothing beyond the representation. That is evidence for putting it
   in the base interface for Cauchy-style carriers, while keeping it a
   separate capability for the Dedekind and lower reals.

## Cost

The dearest declarations are the `<` ones (`lt_of_term`, `lt_respects`,
`lt_cotrans`) and `add_assoc`, each a nested chain of rational estimates.
One finding: the start-index arithmetic (`i <= n` from `i.max(j) <= n`)
was written with `omega` at first, and in `lt_respects` those three calls
were most of the declaration's time. The cost is not the `max` facts. A
probe of the same goal costs about three times more with three unrelated
`Rat` inequalities in scope, because `omega` still unfolds and inspects each
of them (logged on
[omega-fact-arguments](../issues/omega-fact-arguments.md)). Chaining
`le_max_l`/`le_max_r` through `le_trans` costs far less than either, so
`creal` writes its index arithmetic that way.

## Next

- **Multiplication and inverse**
  ([creal-multiplication](../issues/creal-multiplication.md)).
  Multiplication landed in the second round
  ([creal-multiplication-round](creal-multiplication-round.md)), with the
  canonical bound |x_0| + 2 and a cross-index product estimate; the inverse
  has its own issue ([creal-inverse](../issues/creal-inverse.md)).
- **`≤` and the Bishop bridge**
  ([creal-order-and-bishop-bridge](../issues/creal-order-and-bishop-bridge.md)).
  `≤` as `¬(y < x)` and its laws landed with multiplication; left is the
  converse bridge to pointwise equality. The bridge needs the rational lemma "a ≤ b + 1/(k+1)
  for every k gives a ≤ b", which is `same_of_close`'s argument.
- **Completeness:** the diagonal limit of a regular sequence of reals, owned
  by [regular-cauchy-reals](../issues/regular-cauchy-reals.md) and stated
  against [real-completeness-interfaces](../issues/real-completeness-interfaces.md).
