# Regular Cauchy reals

How `lib/std/num/creal.hthr` was built, one section per round in the order they landed (2026-10-16 to 2026-10-31). Each section was its own doc until 2026-11-15; their issue logs still say "round".

- [Regular Cauchy reals, first round](#regular-cauchy-reals-first-round)
- [Regular Cauchy reals, second round: products and `≤`](#regular-cauchy-reals-second-round-products-and-)
- [Regular Cauchy reals, third round: the inverse](#regular-cauchy-reals-third-round-the-inverse)
- [Regular Cauchy reals, third round: Bishop's forms and order with addition](#regular-cauchy-reals-third-round-bishops-forms-and-order-with-addition)
- [Regular Cauchy reals: products against the order](#regular-cauchy-reals-products-against-the-order)
- [Regular Cauchy reals: completeness](#regular-cauchy-reals-completeness)
- [Regular Cauchy reals on dyadic terms at the binary rate](#regular-cauchy-reals-on-dyadic-terms-at-the-binary-rate)
- [Compression, correct rounding of reals, and the first transcendentals](#compression-correct-rounding-of-reals-and-the-first-transcendentals)

## Regular Cauchy reals, first round

Date: 2026-10-16. Starts [regular-cauchy-reals](../../issues/regular-cauchy-reals.md)
on top of the completed rational order ([rational-order-round](rational-order-round.md))
and `calc` over order relations ([calc-order-chains](../tactics/calc-order-chains.md)).
New module [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr); the rational facts
it chains are added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr); the client
is [`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr); the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round covers the representation, the rational embedding, `≈` as a
setoid, negation and addition with their laws, and the strict order with
apartness. Multiplication and completeness come next (the last section).

### The representation

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
those [real-number-foundation](../../issues/real-number-foundation.md) compares.

### Equality: eventually close, with the modulus as data

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

### The rationals inside

`CReal::ofRat(q)` is the constant sequence. It respects `≈`
(`ofRat_respects`) and reflects it (`ofRat_inj`). Reflection needs the new
`Rat::same_of_close`: rationals within every 1/(k+1) of each other are `≈`,
because a positive distance would sit above some 1/(k+1)
(`Rat::archimedean_inv`). It also commutes with `-` and `+` (`ofRat_neg`,
`ofRat_add`), and preserves and reflects `<` (`ofRat_lt`,
`lt_of_ofRat_lt`).

### Negation and addition

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

### Strict order: an eventual gap

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

### Computation: witnesses of theorems evaluate

A `CReal` declaration whose statement carries data is a `theorem` like any
other proof: the `≈` builders and laws (their start indices), the `<`
builders (gap and start), cotransitivity (which side), apartness symmetry
and cotransitivity, and tightness. Their witnesses still compute. A theorem
whose statement carries data keeps its proof sealed beside its opaque
binding, and a projection or `match` stuck on it opens the proof
([theorem-witness-unfolding](../../issues/theorem-witness-unfolding.md)). The
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

### Assumption inventory

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

### What the ordered-field interface learns from a second carrier

For [constructive-ordered-field-interface](../../issues/constructive-ordered-field-interface.md):

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

### Cost

The dearest declarations are the `<` ones (`lt_of_term`, `lt_respects`,
`lt_cotrans`) and `add_assoc`, each a nested chain of rational estimates.
One finding: the start-index arithmetic (`i <= n` from `i.max(j) <= n`)
was written with `omega` at first, and in `lt_respects` those three calls
were most of the declaration's time. The cost is not the `max` facts. A
probe of the same goal costs about three times more with three unrelated
`Rat` inequalities in scope, because `omega` still unfolds and inspects each
of them (logged on
[omega-fact-arguments](../../issues/omega-fact-arguments.md)). Chaining
`le_max_l`/`le_max_r` through `le_trans` costs far less than either, so
`creal` writes its index arithmetic that way.

### Next

- **Multiplication and inverse**
  ([creal-multiplication](../../issues/creal-multiplication.md)).
  Multiplication landed in the second round
  ([creal-multiplication-round](#regular-cauchy-reals-second-round-products-and-)), with the
  canonical bound |x_0| + 2 and a cross-index product estimate; the inverse
  has its own issue ([creal-inverse](../../issues/creal-inverse.md)).
- **`≤` and the Bishop bridge**
  ([creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md)).
  `≤` as `¬(y < x)` and its laws landed with multiplication; left is the
  converse bridge to pointwise equality. The bridge needs the rational lemma "a ≤ b + 1/(k+1)
  for every k gives a ≤ b", which is `same_of_close`'s argument.
- **Completeness:** the diagonal limit of a regular sequence of reals, owned
  by [regular-cauchy-reals](../../issues/regular-cauchy-reals.md) and stated
  against [real-completeness-interfaces](../../issues/real-completeness-interfaces.md).
  It landed in the fourth round
  ([creal-completeness-round](#regular-cauchy-reals-completeness)).

## Regular Cauchy reals, second round: products and `≤`

Date: 2026-10-17. Continues [regular-cauchy-reals-round](#regular-cauchy-reals-first-round)
in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr), with the rational estimates
it needs added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round adds multiplication with its laws modulo `≈`
([creal-multiplication](../../issues/creal-multiplication.md)), and the
non-strict order `≤` as the refutation of `>`, the first half of
[creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md).
The inverse is left to its own round ([creal-inverse](../../issues/creal-inverse.md)).

### The canonical bound

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

### The product

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

### One estimate for every law

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

### `≤` is the refutation of `>`

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

### Computation

The data-carrying lemmas of this round are theorems: `same_close_far` and
`mul_close` carry start indices, and the laws carry them through. This is the
first round that opens sealed proofs in a chain
([theorem-witness-unfolding](../../issues/theorem-witness-unfolding.md)). The
modulus of `mul_comm` at 1 · 1 opens `mul_comm`, then `mul_close`, then two
uses of `same_close_far`, then `same_refl`, and evaluates to 55 by `refl`.
The arithmetic: both bounds are 3, so the factors must agree within
1/((6+1)·2) = 1/14. `same_close_far` asks for halves of that, 1/28, which
regularity grants from index 2·27+1 = 55. The test refuses 54.

A product's terms compute too. The showcase evaluates the first term of
1/2 · 1/3, which reads both constants at index 5.

### Assumption inventory

Nothing new: no choice, no excluded middle, no function extensionality, no
proof irrelevance. `≤` is a negation, and every use of it is a refutation.
Nothing here needs it eliminated classically.

### Cost

Each product law is one `mul_close` instance plus Nat bookkeeping, so the
dearest declarations are `mul_assoc` and `mul_add_distr`, which carry four
far indices each. The start-index arithmetic chains `Nat::le_trans`,
`le_max_l/r`, `le_add_l/r` and `le_succ_r`, never `omega`, for the reason the
first round recorded: `omega` pays for every `Rat` fact in scope. The one
nonlinear identity, `Rat::scale_inv_succ`, needed `ring` in three steps. One
call with all its hints failed to find the combination, so the
denominator of the product is computed first and then related to the target.

### Next

- **The inverse** ([creal-inverse](../../issues/creal-inverse.md)): a real apart
  from zero has a gap 1/(k+1) from some index on, so its terms are at least
  that far from zero, and 1/x reads index (k+1)²(n+1) - 1 past the gap's
  start. `mul_inv` then compares x_a / x_c with 1 across indices, which is
  `same_close_far` again.
- **The Bishop bridge and monotonicity**
  ([creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md)):
  `≈` against pointwise closeness, and `+` and `*` against `<` and `≤`.

## Regular Cauchy reals, third round: the inverse

Date: 2026-10-17. Continues [creal-multiplication-round](#regular-cauchy-reals-second-round-products-and-)
in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr), with the rational estimates
it needs added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`.

This round defines the inverse of a real apart from zero, with
`inv_respects`, `mul_inv` and `inv_mul` modulo `≈`
([creal-inverse](../../issues/creal-inverse.md)).

### The gap

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

### Where the inverse reads

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

### The laws, for any gap

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

### The rational estimates

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

### Computation

The gap is read from the apartness proof's sealed proofs
([theorem-witness-unfolding](../../issues/theorem-witness-unfolding.md)), so the
inverse evaluates. At 0 < 1, `CReal::ofRat_lt` finds k = 1 through
`Rat::archimedean_inv`, the test checks `away_of_apart`'s witness is 1 and
refuses 0, and term 3 of 1⁻¹ is `Rat::one()` by `refl`. The reciprocal of
-2 reads -1/2, and the showcase evaluates term 4 of 2⁻¹ to 1/2.

### Refusals at zero

Zero has no inverse because no gap above or below it can be built. The test
refuses a hand-claimed gap 0 + 1 ≤ 0, while the same claim at 1 is accepted.
It also refuses an inverse asked for without a proof, and it proves that an
apartness proof at zero is absurd. The inverse is not the termwise
reciprocal, and that equation is refused by `refl` too. A wrong field law,
x · x⁻¹ ≈ 0, is refused as well.

### Assumption inventory

Nothing new: no choice, no excluded middle, no function extensionality, no
proof irrelevance. `inv_abs_le` refutes a strict inequality between
rationals, and the rationals' order decides.

### Cost

Each law is one estimate plus Nat bookkeeping, as for products. The start
indices again chain `le_trans`, `le_max_l/r` and `le_add_r`, never `omega`.
The two `ring` identities each take their denominators as hints, in the
pattern of `Rat::mul_sub_mul`, and they went through in one call.

### Next

- **The Bishop bridge and monotonicity**
  ([creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md)).
  With it, `0 < x → 0 < x⁻¹` and the order's interaction with the inverse
  become statable. They are left out here.
- The diagonal completeness construction, after the bridge.

## Regular Cauchy reals, third round: Bishop's forms and order with addition

Date: 2026-10-17. Continues [creal-multiplication-round](#regular-cauchy-reals-second-round-products-and-)
in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr), with two rational facts
added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`. It closes
[creal-order-and-bishop-bridge](../../issues/creal-order-and-bishop-bridge.md).

### Bishop's equality

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

### Bishop's order

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

### Order and addition

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

### Assumption inventory

Nothing new. Every proof into `≤` is a refutation, and the two rational
facts use only the decidable rational order and `archimedean_inv`.

### Cost

Each law here is a few `calc` steps over existing estimates. The dearest is
`bishop_of_le`, which rearranges one sum of six rational terms through
`Rat::add_left_comm` and `Rat::add_add_add_comm` rather than one `ring` call.
Start indices again chain `Nat` lemmas; `omega` appears only on facts with
no `Rat` hypothesis in scope that it would have to unfold.

### Next

- **Products against the order**
  ([creal-mul-order](../../issues/creal-mul-order.md)): `mul_pos` and
  `mul_le_mono` for nonnegative factors. A product's gap needs a lower
  bound on each factor past its gap's start, which the canonical bound
  does not give, so it is not termwise like a sum's.
- **The inverse** ([creal-inverse](../../issues/creal-inverse.md)), in its own
  round.
- **Completeness**: the diagonal limit of a regular sequence of reals.
  Bishop's pointwise forms are the natural statements for its estimates.

## Regular Cauchy reals: products against the order

Date: 2026-10-18. Continues [creal-order-round](#regular-cauchy-reals-third-round-bishops-forms-and-order-with-addition) and
[creal-inverse-round](#regular-cauchy-reals-third-round-the-inverse) in
[`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr), with three rational facts
added to [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr). The client is
[`docs/showcase/creal_client.hthr`](../showcase/creal_client.hthr) and the tests
are `crates/elab/tests/lib_std_creal.rs`. It closes
[creal-mul-order](../../issues/creal-mul-order.md).

```heather
theorem CReal::mul_pos({x, y: CReal}, hx: CReal::zero() < x, hy: CReal::zero() < y): CReal::zero() < x * y
theorem CReal::mul_nonneg({x, y: CReal}, hx: CReal::zero() <= x, hy: CReal::zero() <= y): CReal::zero() <= x * y
theorem CReal::mul_le_mono_r({x, y, z: CReal}, h: x <= y, hz: CReal::zero() <= z): x * z <= y * z
theorem CReal::mul_lt_mono_r({x, y, z: CReal}, h: x < y, hz: CReal::zero() < z): x * z < y * z
```

with `_l` forms through `mul_comm`.

### A positive product is termwise

The issue planned to read both factors past the later gap start and finish
with `lt_of_term`. That is not needed. A product reads both factors at one
index, `mul_at(n)`, which is at or past n. So from the later of the two
starts on, each factor's term is at least its gap, and the term of the
product is at least 1/(k+1) · 1/(l+1) at every index, not at one.
`Rat::inv_succ_mul` names that product as the step 1/(k(l+1) + l + 1), so the
product's gap is data: the product of the gaps, from the later start. The
gap computes, and the client checks that 0 < 1 (gap 1/2) gives 1 · 1 the
gap 1/4.

### A nonnegative product goes through Bishop's form

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

### The monotone forms are algebra

With the two signs in hand, `mul_le_mono_r` is the sign of the difference:
0 ≤ y − x (`sub_nonneg`), so 0 ≤ (y − x) · z, and
x · z ≈ 0 + x · z ≤ (y − x) · z + x · z ≈ ((y − x) + x) · z ≈ y · z.
The strict form uses `sub_pos` and `mul_pos` in the same chain. The round adds
the small additive facts the chain needed (`zero_add`, `sub_add_cancel`, and
right distributivity `add_mul_distr`).

### What is left

Nothing in the issue's scope. Products with the inverse, such as
0 < x ⇒ 0 < x⁻¹ and dividing an inequality by a positive real, need the
inverse's sign. That landed later, generically over the ordered-field
interface ([ordered-field-inverse-sign](../../issues/ordered-field-inverse-sign.md);
`OrderedField::recip_pos` (then `inv_pos`) and its neighbours, at `CReal` through
`CReal::pos_of_mul_pos`).

## Regular Cauchy reals: completeness

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

### The statements

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

### The diagonal

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

### Uniqueness, and limits of rationals

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

### Computation and probes

`complete` is a theorem whose statement carries data, so its witness opens
to `lim` (`complete_witness`, by `refl` at an open sequence), and a limit's
term evaluates (`lim_term` at a literal). The negative controls: the
naturals embedded are not a regular sequence, by evaluation at (0, 3), and
the zero sequence does not converge to 1, by uniqueness.

### Assumption inventory

Unchanged: none. The limit is a function of the sequence, and the
regularity proof is only carried. The usual construction for general Cauchy
sequences uses countable choice to pick a modulus for each real in the
sequence. Here every real's rate is part of its type, so there is nothing to
choose. The only decisions are still the rationals' order on single terms,
and this round takes none.

### Cost

The construction's proofs are each a single chain of rational estimates.
Their cost is of the same shape as `lt_respects` and `bishop_of_le`, which
are dominated by the kernel gate and elaboration of the `calc` steps. One
repeat of the round-1 finding: in `limit_le`, two `omega` calls (a Nat step
`i ≤ 2i+1` and the strict `1/(2k+2) < 1/(k+1)`) were most of the
declaration's time, because `omega` reflects every rational fact in scope.
They became `Nat::le_add_l` and a new `Rat::inv_succ_half_lt`, proved by
`omega` with nothing in scope, and `le_of_close` uses the same lemma.

### Next

- [real-completeness-interfaces](../../issues/real-completeness-interfaces.md):
  `CReal` is now a carrier that inhabits regular-sequence completeness with
  an explicit rate. A capability class would take its statement from here,
  with `Rat` as the carrier expected not to inhabit it.
- Series and the arithmetic of limits (sums, products of convergent
  sequences) are analysis API, not part of this probe;
  [real-functions-and-derivatives](../../issues/real-functions-and-derivatives.md)
  is where they would be asked for.

## Regular Cauchy reals on dyadic terms at the binary rate

Date: 2026-10-30. Closes
[creal-dyadic-binary-rate](../../issues/creal-dyadic-binary-rate.md). The
representation is in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr). Its
clients are the interval enclosures
([`creal_interval.hthr`](../../lib/std/num/float/creal_interval.hthr)), the series
([`series.hthr`](../../lib/std/num/float/series.hthr)), `norm_num` at `CReal`
([`norm_num_real.hthr`](../../lib/std/tactic/norm_num_real.hthr),
[`norm_num.hthr`](../../lib/std/tactic/norm_num.hthr)) and `intervals`
([`interval_tactic.hthr`](../../lib/std/tactic/interval_tactic.hthr)). The probes
live in [`lib/_tests/std/num/creal_tests.hthr`](../../lib/_tests/std/num/creal_tests.hthr).

```heather
record CReal {
    seq: Nat → Dyadic,
    regular: (m, n: Nat) → (seq(m).rat() - seq(n).rat()).abs() <= Rat::inv_pow2(m) + Rat::inv_pow2(n),
}

fn CReal::rounded(f: Nat → Rat, reg: …f's terms within 2^-(m+1) + 2^-(n+1)…) → CReal {
    CReal(λ n => Dyadic::floor_rat(f(n), n + 1), λ m n => CReal::rounded_regular(f, reg, m, n))
}

theorem third_64(): CReal::ofRat(Rat(OfNat(1), 3)).seq(64) = Dyadic(OfNat(12297829382473034410), -65) { refl }
```

### Why

Before this round, the n-th term was an unreduced rational within 1/(n+1).
That made precision cost grow in two ways:

- **Index growth.** k bits meant asking for term 2^k. Indices also multiplied
  as expressions nested: a sum read 2n+1, and a product read (l+1)(2n+2), with
  l taken from the unreduced numerator of x_0.
- **Size growth.** Every sum and product multiplied denominators, so a term's
  size grew with the expression's depth.

Correctly rounded `exp` and `log` need 60+ bits, which is out of reach under
both.

### The representation

The n-th term is a `Dyadic` within 2^-n, so **the index counts bits**:

| operation | reads its arguments at | then |
|---|---|---|
| `x + y` | n + 1 | exact dyadic sum |
| `-x` | n | exact |
| `x * y` | n + 2 + β, β the bit width of the larger canonical bound | rounded |
| `x⁻¹` | past the gap's start, and n + 1 + w out (w the bit width of (k+1)²) | rounded |
| `ofRat(q)` | none | rounded |
| `lim xs` | `xs(n+1).seq(n+1)` | none |

`rounded` floors an exact rational term to n+1 bits. Half the rate pays for
the rounding, so a term's size stays about n + β bits however deep the
expression is. The 64-bit term of 1/3 above is computed by kernel evaluation,
and so is the 64-bit term of 1/3 · 1/3 (its mantissa is in `ninth_64`).

**Proofs stay rational.** `x.at(n)` is `x.seq(n).rat()`, and every estimate
is the rationals' lemma library read through `Dyadic::rat`. No proof does
dyadic arithmetic. The binary helpers are new in `rat.hthr`:

- `Rat::inv_pow2`, `inv_pow2_half` and `inv_pow2_le_inv_succ`;
- `scale_inv_pow2(b, n)`, which says 2^b · 2^-(n+b) ≈ 2^-n;
- `scale_inv_succ_le`, which lets a slack of 8 · 2^-i fit under a 1/(k+1)
  step.

The slack bookkeeping that used to be long `calc` chains is now one `linarith`
call, followed by `scale_inv_succ_le`. That is why `creal.hthr` now imports
`linarith`.

**Public statements keep their shape.** `≈`, `<`, `≤` and `Apart` are
unchanged, and so are the embedding, the class instances
(`OrderedField<CReal>`, `OrderedFieldOfInt<CReal>`) and every law's
statement. `≈` measures closeness in steps of 1/(k+1) and never mentioned the
rate. The design thread kept that eventual `Same` over Bishop's pointwise form
and made this a criterion. Three groups did move to the binary rate:

- the Bishop forms (`BishopSame` and `BishopLe` at 2 · 2^-n);
- `Regular` and `Limit`;
- the term lemmas (`le_term_add` and `term_sub_le` at 2^-n).

### Enclosures are exact

`CReal::enclose(x, n)` is now `[x.seq(n) - 2^-n, x.seq(n) + 2^-n]`. Its
endpoints are dyadics, and no rounding is needed: `CReal::radius(n)` is
`Dyadic(1, -n)`. The old `enclose(n, p)` rounded a rational term outward to
p bits, which was itself a source of width. `RealExpr::enclose` and the
searches lost their p for real leaves. `intervals` reads real leaves at
`n := 32` bits by default, and each try refines the index by one bit
(previously the default was index 1023, doubling per try).

### What changed for clients

- **`series.hthr`.** A series' real is now `CReal::rounded` over its partial
  sums, read at `start + (n + 1) + width(scale)`. The tail bound is restated
  at 2^-(n+1).
- **`Int::divmod`.** It runs on `Nat::ldiv` (long division) instead of the
  unary `Nat::div`. The 64-bit floors run out of fuel otherwise. The quotient
  and remainder lemmas are restated on `ldiv_spec`.
- **`intervals` on inverses.** An inverse reaches the tree as
  `RInv(a, x, h)` with the call's own apartness proof.
  - The tactic host's `View` lists only the arguments a call writes, and an
    inferred or named proof is not one of them. The reader used to fall back
    to a leaf there, and enclosed the inverse by its own terms.
  - That only worked because the old `ofRat(q)` had the constant terms q, so
    the inverse's term did not depend on the index it read. With the proof a
    hypothesis, that index is stuck.
  - The reader now recovers the proof as a hole solved against the node
    (`interval_proof_arg`, the same move `norm_num` already made).
- **`norm_num` leaves.** These are now read without terms. The old reader
  took q back from a term, which only worked because `ofRat`'s terms were q.
  The new one solves a hole `?q` by comparing the leaf with
  `CReal::ofRat(?q)`.
  - A named constant such as `third()` is not that call until it unfolds.
  - The elaborator's unifier pairs rigid spines only when their heads agree.
  - So the tactic host's comparison with holes now retries over the committed
    side's δ/β reducts, one step at a time and at most 16
    (`Unfold::HoleComparison` in `crates/elab/src/oracle.rs`). It never takes the
    weak head normal form, which would unfold `ofRat` too.
  - This is a failure-path retry: a comparison that already succeeds is not
    affected.
- **`norm_num` inverses.** The embedding's inverse now carries the embedding's
  own apartness through `CReal::inv_respects` (`inv_sound`).

### Consequence worth knowing: an inverse depends on its proof up to `=`

`x.inv(h)` reads x at an index computed from the gap that h names. Two proofs
of `x.Apart(0)` can name different gaps, which gives two inverses that are
`≈` but not `=`. That was always so in principle. It was invisible while the
embedded rationals had constant terms, because then the index did not matter.

Now a statement whose `⁻¹` is filled by the search, proved with a generic
theorem's inverse, needs `CReal::inv_respects` to bridge the two proofs. The
ordered-field showcase's `creal_archimedean_inv` shows the pattern.
`inv_respects` takes both proofs as defaulted parameters, so the bridge is
one call.

### Tests

- The creal probes are restated at the binary rate, with new evaluated values:
  - the termwise indices (sum n+1, product by bit width, inverse past the
    gap, limit n+1);
  - the moduli and gaps (`gap_size` 7, `squared` 255);
  - the 64-bit terms;
  - Bishop's identity sequence, which is now not regular at the binary rate.
- `creal_interval_tests` checks exact enclosures: `third_at_10` is
  [680/2048, 684/2048].
- In `interval_tactic_real_tests`, the inverse goals pass through `RInv`,
  including `inv_open_proof`, where the proof is a hypothesis. The refinement
  probes start at index 3.
- `norm_num_real_tests` passes unchanged.
- In `crates/elab/tests/lib_std_creal.rs`, the termwise vacuity controls and
  the strengthened Bishop bound are now refused by the elaborator, as
  mismatches, instead of by the kernel. They compare dyadic terms read as
  rationals, which the elaborator now compares itself.

### Left out

- `Interval::span` is no longer used by `CReal::enclose`. It stays as a
  general rounding constructor.
- Correctly rounded `exp` and `log` (the `float-reals` and
  `float-transcendental` milestones in [the roadmap](../roadmap.md)) were blocked
  on this round, and are not part of it.

## Compression, correct rounding of reals, and the first transcendentals

Date: 2026-10-31. Closes
[creal-compress-and-transcendentals](../../issues/creal-compress-and-transcendentals.md).
It builds on the dyadic rate of [creal-dyadic-round.md](#regular-cauchy-reals-on-dyadic-terms-at-the-binary-rate)
and starts two submilestones of `math-float`: `float-reals` and
`float-transcendental` ([floating-point-design.md](floating-point-design.md)
§6, §8). The code:

- `CReal::compress` in [`creal.hthr`](../../lib/std/num/creal.hthr);
- the relation and the search in
  [`round_real.hthr`](../../lib/std/num/float/round_real.hthr);
- `CReal::log_rat` in [`elementary.hthr`](../../lib/std/num/float/elementary.hthr);
- `Format::exp_fin` and `Format::log_fin` in
  [`transcendental.hthr`](../../lib/std/num/float/transcendental.hthr).

The probes are in
[`transcendental_tests.hthr`](../../lib/_tests/std/num/float/transcendental_tests.hthr)
and [`creal_tests.hthr`](../../lib/_tests/std/num/creal_tests.hthr).

```heather
theorem exp_one_32(): binary32().exp_fin(NearestEven, one32(), 4) = Some(Fin(Finite(False, 11401300, 127, trivial))) { refl }

theorem e_rounds(): RoundsToReal(binary32(), NearestEven, CReal::exp_rat(one32().val()), Fin(Finite(False, 11401300, 127, trivial))) {
    binary32().exp_fin_correct(NearestEven, one32(), 4, Fin(Finite(False, 11401300, 127, trivial)), exp_one_32())
}
```

The first theorem is the kernel computing e to binary32 (0x402DF854). The
second is what that value means: it is the correct rounding of the real
`exp(1)`.

### Compression

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

### The relation at `CReal`

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

### Ziv's search

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

### The search ends

Added the same day by
[float-round-real-termination](../../issues/float-round-real-termination.md).
The probes are in
[`round_real_tests.hthr`](../../lib/_tests/std/num/float/round_real_tests.hthr).

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
[exp-log-grid-gap](../../issues/exp-log-grid-gap.md). Their gap is the Padé
bound, and their series boxes must be shown to narrow.

### exp and log

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
[elementary-functions-at-reals](../../issues/elementary-functions-at-reals.md)
with the rest. So `log_fin_correct` says "the correct rounding of
`CReal::log_rat(f.val())`", which is log by its standard series.

### The Padé gap: exp's search ends

Added the same day by
[exp-log-grid-gap](../../issues/exp-log-grid-gap.md). The code is
[`pade.hthr`](../../lib/std/num/float/pade.hthr), with general lemmas added to
`creal.hthr`, `series.hthr`, `rat.hthr`, `int.hthr`, `round.hthr` and
`round_real.hthr`. The probes are in
[`pade_tests.hthr`](../../lib/_tests/std/num/float/pade_tests.hthr).

```heather
theorem Format::exp_off_grid(self F: Format, x: Rat, hx: ¬(x ≈ 0)): F.OffGrid(CReal::exp_rat(x))
fn Float::exp_total({F: Format}, self x: Float(F), mode: Mode := NearestEven) → Float(F)
theorem Float::exp_total_correct({F: Format}, a: Finite(F), mode: Mode):
    RoundsToReal(F, mode, CReal::exp_rat(a.val()), Float::exp_total(Float::Fin(a), mode := mode))
```

`exp` at every float now has a total, `Option`-free rounding, proved
correct. It is `round_real_apart` over `exp(x)`'s own enclosures
`CReal::enclosed`, which already narrow, with the gap below as `off`.
`Format::exp_search_ends` says the same of the `Option` search: some try
count returns `Some`.

**No integrals.** flean bounds the Padé remainder by an integral. Heather has
no integrals at `CReal`, and does not need one. The remainder is a series:

```
Q_n(x) e^x - P_n(x) = σ_n S_n(x),   σ_n = ±x^(2n+1),
S_n(x) = Σ_k (n+k)! / (k! (2n+1+k)!) x^k
```

`S_n` is an ordinary `Series` (`Series::pade_rem`). Its ratio is exp's
ratio times `(n+k+1)/(2n+k+2)`, which is at most 1, so the ratio is small
wherever exp's is. The identity is proved by induction on `n`, from
the three-term recurrence `S_n = (4n+6) S_{n+1} + x² S_{n+2}` and the two
base cases `e^x = 1 + x S_0 = -1 + 2 S_0 + x² S_1`. Each of these is first
proved between terms, then between partial sums, then between the limits:

- **Terms.** A term is exp's term times a weight
  `w(n, k) = (n+k)!/(2n+1+k)!` that does not mention `x`. The recurrence
  becomes one field identity among weights,
  `(2n+k+4)(2n+k+5) = (4n+6)(n+k+3) + (k+1)(k+2)`. Stated with `x` in it,
  the same identity ran out of the kernel's fuel. Without `x`, and with the
  reciprocals bound by `let` so that `ring` reads them as atoms, it is cheap.
- **Sums.** `Series::sums_comb`: if a linear relation holds at the first
  partial sums and between every later term (at fixed offsets), it holds at
  every later partial sum.
- **Limits.** `Series::comb`: then it holds between the limits. Each limit
  is within its tail bound of every partial sum, and `CReal::le_of_slack`
  closes the gap of `2^-m` for every `m`.

**Integers.** Clearing denominators at `x = u/v` gives `q_n = v^n Q_n(u/v)`
and `p_n = v^n P_n(u/v)`. They satisfy
`a_{n+2} = (4n+6) v a_{n+1} + u² a_n`, so they are integers by
construction (`PadeInts`). `PadeInts::bridge` ties them to the rational
approximants. Their Casoratian `p_n q_{n+1} - p_{n+1} q_n` is `-2u` times
`(-u²)^n`, so it is never 0 (`PadeInts::cas_pos`).

**Size.** `|S_n|` is at most `n!/(2n+1)!` times `K`, where `K` is the
tail-bounded partial sum of `e^|x|` (`CReal::pade_rem_bound`, by
`Series::real_dominated`). So the integer error
`|q_n e^x - p_n| <= |v^n σ_n| n!/(2n+1)! K`. These bounds are the terms
of a series with ratio `v x²/(4n+6)` (`Series::pade_beta`), and a series'
`fine` index gives two consecutive terms below any `2^-m`.

**Apartness.** Take a lattice point `g = G·2^-d`. Then `q_n g - p_n` is an
integer multiple of `2^-d`. It is nonzero at `n` or at `n+1`, because if
both vanished the Casoratian would too (`PadeInts::not_both_zero`). So it is
at least `2^-d`, while the error is below `2^-(d+2)`. Then
`q (e^x - g) = (error) - (q g - p)` keeps `e^x - g` away from 0 by
`2^-d / (2(|q_n| + |q_{n+1}|) + 2)`, a distance that does not depend on `g`
(`CReal::apart_of_scaled`, `CReal::exp_apart_lattice`). The grid is such a
lattice (`Format::grid_lattice`). A real a fixed distance from every grid
point is off the grid (`Format::off_grid_of_apart`, which only reads the two
ends of the cell holding a rational approximation).

**What the gap does not give yet.** It does not make `Float::exp` (the
`Option` search over the series boxes `CReal::exp_box`) end, because those
boxes have no narrowing proof
([exp-box-narrowing](../../issues/exp-box-narrowing.md)). And it does not cover
log. log's gap is exp's gap read through `exp(log q) ≈ q`, a law that is
not proved
([log-grid-gap](../../issues/log-grid-gap.md)). `Float::exp_total` is not
evaluated in the probes. Its try count is computed through the proofs (the
Padé index, the Archimedean bound on the distance), and nothing has measured
that cost.

### What computes today

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
[interval-evaluation-budget](../../issues/interval-evaluation-budget.md), a
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

### Left out

- **IEEE specials:** done since, as `Float::exp` and `Float::log` over every
  float ([float-exp-log-specials](../../issues/float-exp-log-specials.md)):
  exp(±∞), exp(±0) = 1 exactly, log(±0) = -∞, log of a negative number and
  log(-∞) invalid, NaN in, NaN out. log(1) = +0 exactly is still the search
  ([float-log-one-exact](../../issues/float-log-one-exact.md)).
- **The Padé gap for log**, and narrowing of the series boxes: exp's gap is
  the section above. log's waits on `exp(log q) ≈ q`
  ([log-grid-gap](../../issues/log-grid-gap.md)), and the boxes'
  narrowing is [exp-box-narrowing](../../issues/exp-box-narrowing.md).
- **Argument reduction for exp:** a large argument starts its series far out
  ([interval-log-and-reduction](../../issues/interval-log-and-reduction.md)).
- **The generic `RoundsTo` over an ordered field:** the transfer lemma of §6.
  `RoundsToReal` is its `CReal` instance, stated without it.
- **Faithful rounding without side conditions** (§6): not built. Ziv's
  search answers the correct-rounding question directly.

