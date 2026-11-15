# `linarith`: linear arithmetic at an ordered field, up to `≈`

Date: 2026-10-27. Owner: [linarith-ordered-fields](../../issues/linarith-ordered-fields.md).

- [`lib/std/tactic/linarith.hthr`](../../lib/std/tactic/linarith.hthr): the
  certificate lemmas, generic over `OrderedField + CommRingOfInt`, checked once.
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
with `OrderedField` and `CommRingOfInt` instances (`Rat`, `CReal`) when it follows
linearly from the facts; with facts that contradict each other it proves any
goal. A fact is a `<`, `<=`, `≈` or `¬(x < y)` at the goal's carrier, its
type read through a head β-redex as `omega` reads one (a pattern-bound
`Exists` proof, typed by its predicate applied to the witness,
issues/linarith-redex-typed-fact.md). The
written facts (`linarith(h₁, …)`, any expression, as `omega(h, …)` takes
them) are tried first; when they do not suffice, every such fact in the
context is added, block `let` facts among them. A term that is not linear —
a product of two non-constants, a reciprocal, a function application, a
field read — is an atom, so `x * y <= z` is a fact about the atom `x * y`;
a reciprocal whose denominator a fact shows positive is cleared (§5).

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
(docs/tactics/ring-normalization-design.md §8). `lin_finish_le` reads `a <= b` back:
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

**The interface.** The section's constraint is
`<A: OrderedField(≈, <, <=, +, *) + CommRingOfInt(≈, +, *)>`. The lemmas need
both: the order laws to combine facts, and the carrier's integers to state
coefficients `ring` reads as numerals. The two constraints share `≈`, `+` and
`*` at `A`, so they are one dictionary of the synthesized class
`CommRingOfInt+OrderedField`, with `CommRing` once under both
(docs/language/classes/operators-onto-classes-design.md §17). At `Rat` and `CReal` it is
assembled from the carrier's two instances. Until 2026-10-31 this was a
hand-written combined class, `OrderedFieldOfInt`, with an empty instance at
each carrier; issues/constraints-sharing-indices.md retired it.
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
instance for `OrderedFieldOfInt<A>(…)`", in the class's day; now the
same shape names `CommRingOfInt+OrderedField`).

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
([ring-field-read-atom-spelling](../../issues/ring-field-read-atom-spelling.md)).
`linarith` meets those atoms in every `CReal` regularity step, through the
`ring` step it generates, so the fix is part of this round: an atom that does
not spell is named in the list by an alias bound to the term (`__ring_a{i}`),
and the list's value is the term itself. `ring` alone gains the same: a
`CReal` estimate over `x.seq(n)` is a `ring` goal now.

## 5. Positive denominators

[linarith-positive-denominators](../../issues/linarith-positive-denominators.md).
A reciprocal is an atom to the search, so `a * d⁻¹ <= b` was a fact about
the monomial `a·r`, unrelated to `a`. Given `0 < d` it is `a <= b * d`, and
`linarith` now reads it that way too:

```heather
theorem goal(a, b, d: Rat, hd: 0 < d, h: a <= b * d): a * d⁻¹ <= b { linarith(hd, h) }
theorem fact(a, b, d: CReal, hd: 0 < d, h: a * d⁻¹ < b): a < b * d { linarith(hd, h) }
theorem built(n: Nat, a, b: Rat, h: a <= b * (Rat::ofInt(OfNat(n)) + 1)): a * Rat::inv_succ(n) <= b { linarith(h) }
```

**The reading.** `ring`'s reader already meets each reciprocal `r` with
its fact `r·d ≈ 1` (`<op>_mul`, `Rat::inv_succ_cancel`); `FieldReading`
now keeps, per reciprocal, the denominator `d` that fact names
(`ring::Reciprocal`). A denominator is a *factor* when a strict fact shows
it positive: one whose difference is `d` itself (`0 < d`, written or in
context), or one whose difference is `r` (`0 < x⁻¹`), and then
`lin_den_pos` gives `0 < d` from `s·d ≈ 1`, the identity by `ring`.
`Rat::inv_succ(n)` is positive by construction: the reading hands its
`Rat::inv_succ_pos(n)` over as a fact, so `inv_succ`'s denominator is a
factor with nothing written.

**The rows.** Every row that mentions a factor's `r` — the facts', and the
goal's negation — is offered as well multiplied by `d`, its form reduced by
`r·d = 1`: a monomial carrying `r` loses one `r`, any other is multiplied by
`d`'s form. That is exact modulo the reciprocal's fact, so the scaled row is
the same inequality, and the original stays offered. A row is multiplied
by at most two denominators (two fractions on one side, as
`a * d⁻¹ <= b * e⁻¹`), each once. The products the scaling makes
(`b·d`) are monomials like any other: Fourier–Motzkin treats each as a
variable, and the facts it is compared with mention the same ones.

**The certificate.** A scaled fact's part is `P·(hi − lo)`, proved by
`lin_scale_le`/`_lt` with `P` the product of its factors (`lin_scale_lt`
chains their positivity). A scaled goal row changes the goal's multiplier:
it is no longer a numeral `k` but `K = Σ λⱼ·Pⱼ` over the goal's uses, each
term positive (a numeral by `lin_num_pos`, a product by `lin_scale_lt`), the
sum by `lin_add_lt_lt`. `lin_finish_le`/`_lt` already took any positive
`k`, so `K·(b − a) ≈ s` is read back as before. The identity now holds only
modulo `r·d ≈ 1`; `ring` reads the same reciprocals with their facts and
clears them exactly (docs/tactics/ring-normalization-design.md §9), so it checks it
with no hint. A denominator whose sign is unknown is never a factor, and a
negative one is not either: `d < 0` reverses the inequality, and the probes
hold both as refusals.

**Cost.** Nothing changes for a problem with no reciprocal factor. With
`f` factors a row has at most `1 + f + f²` uses, so the elimination's input
grows by that factor; the problems this is for have one or two.

## 6. Not in this round

- **A generic carrier.** Inside a `section<A: OrderedField(…)>` the reading
  needs a concrete carrier with designated operations, as `ring`'s relation
  reading does.
- **`Int`/`Nat`.** Built later: §8.
- **Products of facts** (`nlinarith`, designed in
  [nonlinear-arithmetic-design](nonlinear-arithmetic-design.md)), and
  `¬(x <= y)` facts, which at `CReal` do not give `y < x`.

## 7. Cost shape

The search is cheap next to the certificate. A certificate is one `ring`
identity over the atoms the facts mention plus one lemma application per
used fact, so its gate cost is `ring`'s normalization at degree one —
linear in the facts' size — and the conversions that read each generic
lemma at the carrier unfold one instance projection per operation node.

## 8. `Int` and `Nat`: `ring`'s monomials as `omega`'s atoms

Date: 2026-10-28. Owner: [ring-inequalities](../../issues/ring-inequalities.md),
its Int-atom route.

```heather
theorem commuted(a, b, c: Int, h: a * b <= c): b * a + b <= c + b { linarith(h) }
theorem rounding(x, y: Int, h: OfNat(2) * (x * y) <= OfNat(1), hp: OfNat(0) < y * x): False { linarith(h, hp) }
theorem defined(s, d, p, e, t: Int, h: d = p * e, k: s * d <= t): s * p * e <= t { linarith(h, k) }
theorem Rat::mul_le_mono_r_nonpos({x, y, z: Rat}, h: x <= y, hz: z <= 0): y * z <= x * z {
    let flipped = Rat::mul_le_mono_r(x := x, y := y, z := -z, h := h, hz := …);
    linarith(flipped)
}
```

At `Int` and `Nat` the decision procedure is `omega`'s, which reads a
product of two non-numerals as one atom by its spelling: `a * b`, `b * a`
and the `a * b` inside `(a + 1) * b` are three unrelated atoms to it. That
was the whole gap. Before this, a client stated the link by hand, one
`let … = ring` per product, and handed them to `omega`
(`Rat::mul_le_mono_r` stated two, `mul_le_mono_r_nonpos` six).

**The certificate is those lets, written by the tactic.** Every side of the
goal and of the written facts — `<=`, `<`, `=` at `Int` or `Nat`, their
negations, and a defined proposition that unfolds to one, as `omega` reads
them (`omega_cert::integral_sides`) — is read by `ring`'s reifier at its
own carrier (`FieldReading::integral`, one atom table per carrier). A side
that multiplies two non-numerals is stated equal to its normal form, a
linear form over monomials, each monomial spelled one way (its atoms'
aliases in atom order), and the statement is proved by `ring`. Then

```text
{ let __lin_b0: (side₀ = form₀) = ring; …; omega(facts…, __lin_b0, …) }
```

`omega` meets each monomial as one atom wherever it occurs, and the rest is
its: the search, strictness as `+ 1`, the integers' rounding (`2·xy ≤ 1`
and `0 < yx` is a contradiction over `Int`, not over `ℚ`), and its own
reading of the context. Nothing is decided here; a side `ring` cannot read
is left to `omega` as written. A side whose normal form is linear still
gets its statement when its spelling multiplies (`x * (y - y)`), since
`omega` would read that product as an atom.

**Equations that define an atom.** A written equation `t = e` (or
`e = t`) whose one side reads as an atom alone, not mentioning `e`, is a
substitution: every side mentioning `t` is stated equal to its form with
`e` for `t`, proved by `ring(h)`, whose multiplier search finds the rest of
the monomial. That is what the rationals' order laws needed:
`(a * e) * (y * z).den.int()` is the monomial `a·e·q·r` given
`y.den_mul(z): (y * z).den.int() = y.den.int() * z.den.int()`. Definitions
are applied to a fixed point; atoms defined in terms of each other are a
refusal.

**Choosing the route.** An ordered-field goal (`OrderedField` and
`CommRingOfInt` at the carrier) is read
at its field first, since its order unfolds to one at `Int`; then an
integral goal; for any other goal the first written fact (else context
fact) that reads either way decides. When the field reading finds no
combination and the goal unfolds to an `Int` relation (`Rat::Le` is a
cross-multiplication), the integral route is tried, as `ring` falls back to
the unfolded equation (`Rat::mul_le_mono_r_nonpos` above). The written
facts' sides are read first; when that certificate fails, the context
facts' sides are read too, and it is retried only if that added a product
to state.

**A refusal** shows each side as read (`` `b * a` as `a * b` ``), the line
`omega` stopped with, and the certificate.

**Not here.** Products of facts (`0 <= x * x` is refused; nlinarith's
degree-two products would be new rows), and atoms that do not spell, which
`omega` cannot name (a real's `x.seq(n)` is `Rat`'s, read at the field).

**Cost.** One `ring` normalization per multiplying side, at that side's
degree, plus `omega` over the facts and those equations; the monomials are
atoms to it, so its problem is the size the hand-written version had.


## 9. Conjunctions, and the definitions that unfold to them

Date: 2026-11-06. Owner: [linarith-conjunctions](../../issues/linarith-conjunctions.md).

```heather
section<K: OrderedField(≈, <, <=, +, *)> {
theorem LocatedAddGroup::abs_le_nonneg(z, e: K, hz: AbsLe(z, e)): K.unit <= e { linarith(hz) }
theorem LocatedAddGroup::abs_le_sum2(a, b, r, x, y, c: K, ha: AbsLe(a, x), hb: AbsLe(b, y),
    hr: r ≈ a + b, hc: x + y <= c): AbsLe(r, c) { linarith(ha, hb, hr, hc) }
}
```

The analysis library states its bounds as predicates — `AbsLe(z, e)` is
`Within(<=, -e, z, e)`, which is `-e <= z ∧ z <= e`; `AbsLt`, `Close` and
`Between` alike — and before this round `linarith` read neither a
conjunction nor a definition of one. Every client split them by hand:
`linarith(hz.left, hz.right)` for a fact, and
`abs_le_intro(z, e, linarith(…), linarith(…))` for a goal, each side handed
its own half of every fact.

**Facts.** A fact whose type is a conjunction, or whose head unfolds to one
(the first reduct that is a conjunction or a relation, as `omega` unfolds a
defined proposition, `omega_cert::unfolded_proposition`), gives each side
through its projection, recursively, named `h.left`/`h.right` in a refusal.
That holds for written facts, at the field route and at `Int`/`Nat` (where
each side is a fact `omega` is given), and for the context's: the context
pass now reads `local_fact_entries`' evidence directly, since a projection
is no name `resolve_reading` resolves (the context's literal conjunctions
had been dropped silently). A side that is no relation at the carrier is
passed over, as a context fact is; a written fact none of whose sides reads
is still a refusal.

**Goals.** A goal that is a conjunction, or unfolds to one, is proved side
by side, each side by the same call with the same facts, and paired with
`logic::And`. The sides are the conjunction's type arguments
(`display_targs`), so a refusal names the side as a side of the goal as
written — "could not prove the left side of `AbsLe(z, e + z)`" — rather than
spelling the unfolded side, whose `-e` at a class carrier is a projection of
the parent class's dictionary.

**Refusals at a class carrier** spell the goal with its operators and its
carrier, `K.unit <= d * d + K.unit`, not the section's placeholders
`#op<=@0_2(#constraint0.unit, …)` (`resugar`, which reads an operator
binder's symbol back off its generated name, `traits::op_index_symbol`).

**Cost.** A split fact is two rows where one hand-picked half was one: the
library sweep that dropped `abs_le_intro` hands both sides every fact, so
the elimination sees more rows per call. Unfolding is tried only for a
fact that reads as neither, with a global head, and stops at the first
reduct that reads.

**Not here.** `Rat::abs` and `CReal::abs` as functions (`|t|` read as an
atom with `±t <= |t|`, and `|t| <= e` proved through `Rat::abs_le`); `∨`
facts (a case split per disjunction); `↔`.
