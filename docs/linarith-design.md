# `linarith`: linear arithmetic at an ordered field, up to `≈`

Date: 2026-10-27. Owner: [linarith-ordered-fields](../issues/linarith-ordered-fields.md).

- [`lib/std/tactic/linarith.hthr`](../lib/std/tactic/linarith.hthr): the
  certificate lemmas, generic over `OrderedFieldOfInt`, checked once.
- `crates/elab/src/linarith.rs`: the tactic — reading, elimination, the
  certificate's text.
- `lib/_tests/std/tactic/linarith_tests.hthr`: probes at `Rat` and `CReal`,
  and refusals.

## 1. What a client writes

```heather
import linarith;

theorem shift(a, q, e, f, r: Rat, h: a <= q + (e + r), ef: e <= f): a <= (q + r) + f { linarith(h, ef) }
theorem scaled(x, y: CReal, h1: 2 * x + y < 3, h2: x - y <= 0): x < 1 { linarith(h1, h2) }
theorem rearrange(b, u, c: CReal): (b + u) - c ≈ (b - c) + u { linarith }
theorem absurd(x: Rat, h1: x < 0, h2: 0 < x): False { linarith(h1, h2) }
```

`linarith` proves `a <= b`, `a < b`, `a ≈ b` or `¬(a < b)` at a carrier
with an `OrderedFieldOfInt` instance (`Rat`, `CReal`) when it follows
linearly from the facts; with facts that contradict each other it proves any
goal. A fact is a `<`, `<=`, `≈` or `¬(x < y)` at the goal's carrier. The
written facts (`linarith(h₁, …)`, any expression, as `omega(h, …)` takes
them) are tried first; when they do not suffice, every such fact in the
context is added, block `let` facts among them. A term that is not linear —
a product of two non-constants, a reciprocal, a function application, a
field read — is an atom, so `x * y <= z` is a fact about the atom `x * y`.

`linarith` follows the bare-form shadowing rule of `omega` and `ring`.

## 2. The certificate

The issue asked for a certificate that is a nonnegative combination of the
hypotheses, checked through the `OrderedField` laws so that it holds at any
instance. That is what is written, in the form that needs no refutation:

```text
k·(b − a) ≈ Σ λᵢ·(hiᵢ − loᵢ) + c          k > 0, λᵢ > 0, c ≥ 0
```

Each fact `loᵢ R hiᵢ` makes its difference nonnegative (`lin_le_part`,
`lin_lt_part`, `lin_same_part` and `_rev` for the two directions of an
equation, `lin_not_lt_part`), a positive numeral scales it (`lin_scale_le`/
`_lt`, the numeral's positivity by `lin_num_pos`), and the parts add up
(`lin_add_le_le` … `lin_add_lt_lt`, strict as soon as one summand is). The
identity is `ring`'s: the certificate states it as a `let` and proves it with
`ring`, which normalizes both sides at the carrier
(docs/ring-normalization-design.md §8). `lin_finish_le` reads `a <= b` back:
`0 ≤ s ≈ k·(b − a)` with `k` positive. `lin_finish_lt` reads `a < b` when
the sum is strictly positive, which a strict fact with a positive multiplier
or a positive `c` makes it. When the goal's multiplier `k` is zero the facts
alone give `0 < s ≈ 0`, and `lin_finish_false` closes `False` (any other
goal by `false_elim`). `≈` is the two orders and `le_antisymm`; `¬(a < b)` is
`b <= a` and `not_lt_of_le`.

**Why the direct form.** `a <= b` is Bishop's `¬(b < a)`, so the textbook
certificate — assume the negation, sum to `0 < 0` — is a refutation, and is
valid at `CReal`. The direct form is the same combination solved for the
goal's difference (Farkas: if the negation was used, its multiplier is `k`),
so it costs nothing more, and it proves `a < b` too, which no refutation
can at `CReal`: there `<` is positive data. Nothing in the certificate
decides an order, and nothing unfolds the carrier.

**The interface.** `OrderedFieldOfInt` (lib/std/algebra/ordered_field.hthr)
is `OrderedField` and `CommRingOfInt` over the same ring, with nothing added.
The lemmas need both — the order laws to combine facts, the carrier's
integers to state coefficients `ring` reads as numerals — and one constraint
cannot be written as two: each would install `≈`, `+` and `*` again. Its
instances sit right after `OrderedField<Rat>` and `OrderedField<CReal>`.
`rat.hthr` imports `linarith` (which imports neither carrier), so the laws
after the instance use it: `Rat::neg_gap`, `le_add_shift` and
`sub_le_shift`, which existed only to state such steps, are one call each.

**How the text is written.** The certificate names the goal's and the facts'
terms through aliases (`__lin_t{i}`), never their spelling, so a term that
does not spell (a real's term `x.seq(n)`) is still one `linarith` reads. A
difference is written `hi + -lo`, not `hi - lo`: when a generic lemma's
application is checked, its statement is matched against the expected type
to fix the class's operations before the instance is found, and that match
does not unfold `Rat::sub` to the lemma's `b + A.inv(a)` (it fails as "no
instance for `OrderedFieldOfInt<A>(…)`").

## 3. The search

Each side of the goal and of every fact is read by `ring`'s reifier at the
carrier (`ring::FieldReading`), one atom table for all of them, so the two
agree on what an atom is: the identity `ring` checks is over exactly the
monomials the search saw. A fact's row is `hi − lo` as a linear form over
the nonconstant monomials, `≥ 0` or `> 0`; the goal's negation is one more
row (`a − b > 0` against `a <= b`, `≥ 0` against `a < b`).

Fourier–Motzkin elimination finds the combination. Rows carry their origin
(the multiplier of each input row), combine with positive integer
multipliers and are divided by the gcd of everything they carry; for each
linear part only the strongest row is kept. The variable eliminated next is
the one adding the fewest rows. A row with no variables that is negative, or
zero and strict, is the contradiction, and its origin the `λ`. The search
gives up past 2048 rows: elimination is doubly exponential in the worst case,
and goals with that many interacting facts are not what this is for. The
combination is recomputed and checked before it is written, so a searcher
bug is an internal error, not a `ring` failure.

The written facts are tried alone first because context facts make the
elimination larger and are usually not needed; the second pass is the
convenience of not naming every fact.

When nothing is found the refusal shows each fact as it was read
(`d: f + c - a >= 0`), which is what catches a term the author meant as one
atom being two.

## 4. `ring` names atoms it cannot spell

`ring` elaborated its atom list from the atoms' spellings, so an atom with
none refused the whole reading
([ring-field-read-atom-spelling](../issues/ring-field-read-atom-spelling.md)).
`linarith` meets those atoms in every `CReal` regularity step, through the
`ring` step it generates, so the fix is part of this round: an atom that does
not spell is named in the list by an alias bound to the term (`__ring_a{i}`),
and the list's value is the term itself. `ring` alone gains the same: a
`CReal` estimate over `x.seq(n)` is a `ring` goal now.

## 5. Not in this round

- **Denominators.** The inequality form [field-simp](../issues/field-simp.md)
  left here — multiply a fact by a positive denominator, `a * d⁻¹ <= b` to
  `a <= b * d` given `0 < d` — is not done: `lin_scale_le` already takes any
  positive factor, but the search would have to multiply rows by atoms and
  reduce `r·d` to `1`, which is a nonlinear preprocessing step. A fact that
  relates reciprocals linearly (`Rat::inv_succ_half`) can be passed as a
  written fact today. Filed as
  [linarith-positive-denominators](../issues/linarith-positive-denominators.md).
- **A generic carrier.** Inside a `section<A: OrderedField(…)>` the reading
  needs a concrete carrier with designated operations, as `ring`'s relation
  reading does.
- **`Int`/`Nat`.** `omega` owns them; [ring-inequalities](../issues/ring-inequalities.md)'s
  Int-atom route stays open, and this file's reader is the normaliser it
  would share.
- **Products of facts** (`nlinarith`), and `¬(x <= y)` facts, which at
  `CReal` do not give `y < x`.

## 6. Cost shape

The search is cheap next to the certificate. A certificate is one `ring`
identity over the atoms the facts mention plus one lemma application per
used fact, so its gate cost is `ring`'s normalization at degree one —
linear in the facts' size — and the conversions that read each generic
lemma at the carrier unfold one instance projection per operation node.
