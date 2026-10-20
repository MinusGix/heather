# The constructive ordered-field interface

For [constructive-ordered-field-interface](../issues/constructive-ordered-field-interface.md).
The module is `lib/std/ordered_field.hthr`; its instances are at the end of
`lib/std/rat.hthr` and `lib/std/creal.hthr`; the client is
`docs/showcase/ordered_field_client.hthr`, checked with the controls in
`crates/elab/tests/lib_std_ordered_field.rs`.

## What both carriers share

The two carriers were written before the interface, and the interface is
what they turned out to have in common
([regular-cauchy-reals-round](regular-cauchy-reals-round.md), "What the
ordered-field interface learns"):

- a setoid `≈` that is an `Equivalence`, never `=`;
- a strict order `<` that is positive data (a cross-multiplied integer gap at
  `Rat`, a rational gap from some index on at `CReal`), irreflexive,
  transitive, invariant under `≈`, cotransitive, and tight;
- a `≤` that means `¬(y < x)`: definitionally at `CReal`, by two `omega`
  lemmas at `Rat`;
- an abelian group under `+` with translation-invariant `<`;
- a commutative multiplication, `0 < 1`, products of positives positive, and
  an inverse that takes apartness from zero instead of returning a junk
  value;
- the Archimedean property: every element is below some natural number.

Neither carrier decides anything the interface asks for. `Rat` has
trichotomy, `le_dec` and a decidable `≈` as extras; `CReal` has none of
them, and nothing in the interface mentions them. The controls check that no
member of any layer decides.

## The layers

Each layer is a class indexed by its relations and operations, in the
library's convention (`relation_props`, `algebra_rel`): `≈`, `<`, `≤`, `+`
and `*` are indices, never fields, so one carrier could carry two orders.
Zero, one, negation, the inverse and the embedding of `Nat` are fields, as
`Group`'s inverse is.

| Layer | Adds | What first needs it |
|---|---|---|
| `StrictOrder(≈, <, ≤)` | `Equivalence(≈)`; `<` irreflexive, transitive, respecting `≈`, tight; `≤` ⇔ `¬>` | open intervals, apartness laws, `≤` reflexive and antisymmetric modulo `≈` |
| `Cotransitive(<)` | `x < y → x < z ∨ z < y` | (a capability, alone) |
| `PseudoOrder` | the two above | `≤` transitivity, mixed `<`/`≤` steps, closed intervals, apartness cotransitivity |
| `OrderedAddGroup(≈, <, ≤, +)` | `StrictOrder`, `algebra_rel`'s `SemigroupRel`/`Commutative` at `+`, zero, negation, `<` translation-invariant | group algebra, `≤` translation, the bounded triangle inequality, tightness of bounds |
| `LocatedAddGroup` | `OrderedAddGroup` and `PseudoOrder` | a sum's gap splitting between summands, a bound's positivity, `≤` bounds |
| `OrderedField(≈, <, ≤, +, *)` | one, `of_nat`, the inverse at apartness, ring laws, `0 < 1`, `mul_pos`, Archimedean | strict monotonicity of products, uniqueness and invariance of the inverse |

Two decisions in that table are worth their reasons.

**The `<` laws are fields, not the `Irreflexive`/`Transitive` parents.**
`Equivalence(≈)` already contains `Transitive(≈)`; adding `Transitive(<)`
puts the same class into one dictionary at two indices, which the class
system refuses unless the parents are tagged, and tagged parents are not
what `calc` or resolution look through. The carriers' existing
`Transitive<Rat>(Rat::Lt)` instances stay as they are.

**`≤` is an index with two laws, not a derived definition.** The issue's
2026-10-16 note asked for `<` primitive and `≤` as `¬(y < x)`. Taking `≤` as
an index constrained by `le_of_not_lt`/`not_lt_of_le` keeps exactly that
meaning while letting each carrier keep its own spelling: at `CReal` the two
laws are the identity, and at `Rat` generic results arrive in `Rat::Le`, the
relation the rest of `rat.hthr` uses, rather than in a negation a client
must convert.

## Locatedness is a separate capability

The issue asked whether locatedness belongs in the base interface. The
answer the theorems give is: no, but every interface a carrier here fills
includes it.

`Cotransitive(<)` is its own class, and `PseudoOrder` is `StrictOrder` plus
it. Everything in `StrictOrder::` was proved without it, and the controls
show the two places it is first needed are refused one layer down:

- `≤` is transitive only where `<` is located. From `z < x` cotransitivity
  places `y`, and either side contradicts a hypothesis. Without it,
  `¬(y < x)` and `¬(z < y)` say nothing about `z` and `x`. The same holds
  for the mixed steps `x < y ≤ z` and `x ≤ y < z`.
- A bound with a point under it is positive (`-e < x < e ⇒ 0 < e`). The
  proof uses locatedness: `-e < e` places `0`, and `0` below `-e` makes `e`
  positive by negation. The group laws alone give `0 < e + e`, and the
  interface has no way to halve.

So the line falls between what the laws of a tight strict order and an
ordered group give (open intervals, apartness, antisymmetry, the triangle
inequality on open bounds, "within every positive bound means equal") and
what cotransitivity adds (closed intervals and the `≤` forms). A carrier
whose `<` is not cotransitive, such as the Dedekind reals without located
cuts, could fill the lower layers and would have to prove the rest by its own
means. Both carriers here are located, `Rat` by decision and `CReal` by its
approximations, and both fill every layer.

`Cotransitive` belongs with the relation properties in `relation_props`. It
lives in `ordered_field` for now because the x86 modules import
`relation_props`, so adding a class there invalidates every native image for
no consumer; it moves when a second module wants it.

## Absolute value as a bound

`CReal` has no `abs` and no `max`, and needs neither for the estimates the
interface states. `AbsLt(x, e)` is the open interval `(-e, e)`, `AbsLe` the
closed one, and `Close(x, y, e)` is `AbsLt(x - y, e)`. The theorems are about
bounds, not about a function:

- `OrderedAddGroup::abs_lt_add` (the triangle inequality), `abs_lt_neg`,
  `abs_lt_mono`, `close_sym`, `close_triangle`;
- `OrderedAddGroup::same_zero_of_abs_lt` and `same_of_close`: a point within
  every positive bound of zero is zero. This is tightness, not locatedness:
  `x > 0` fails the bound `x` and `x < 0` fails the bound `-x`.
- `LocatedAddGroup::abs_lt_pos`, `abs_le_add`, `abs_lt_of_abs_le`.

At `Rat`, `AbsLt(x, e)` unfolds to `-e < x ∧ x < e` with `Rat::neg` and
`Rat::Lt`, and the client passes hypotheses in that form. A carrier with
`abs` can connect it by one lemma (`|x| < e ⇔ AbsLt(x, e)`); `Rat` does not
need to yet.

## The inverse, positivity and the Archimedean property

The inverse is `inv: (x: A) → ApartBy(<, x, zero) → A`, the same shape as
`x⁻¹` at both carriers (`x.inv(h := infer)` over `x.Apart(0)`); the
instances pass the proof through, and `refl` shows the field is the
carrier's own `x⁻¹`. `OrderedField::inv_unique` and `inv_respects` are
proved once from `mul_inv` and the ring laws, so the inverse is independent
of the apartness proof that built it at every carrier. `CReal` had
`inv_respects` already, proved through gaps; it gets `inv_unique` for free.

Positivity is `0 < x` (both carriers' `Positive` unfold to it).
`mul_pos` is a law, and strict monotonicity of products is derived from it
through distributivity.

The Archimedean law is "every element is below some `of_nat(n)`", with
`of_nat` a field whose two laws (`of_nat(0) ≈ 0`, `of_nat(n+1) ≈ of_nat(n) +
1`) let each carrier keep its own embedding. `CReal` did not have it; it
does now (`CReal::archimedean`): a real is below one past its canonical
bound, since every term is at most the bound, so the gap of one holds from
index zero.

## The inverse's sign

For [ordered-field-inverse-sign](../issues/ordered-field-inverse-sign.md).
The inverse of a positive being positive needs multiplication to reflect
positivity: `0 < x` and `0 < x * y` give `0 < y`. That is a law of
`OrderedField` (`pos_of_mul_pos`), not a theorem, because the other laws
cannot produce it. From `mul_pos` and the ring laws, `y ≤ 0` gives
`x * y ≤ 0`, so `0 < x * y` refutes `y ≤ 0`; but refuting `y ≤ 0` is
`¬¬(0 < y)` in Bishop's reading, and a gap cannot be read off a
refutation. The law is strong extensionality of `*` at zero (a product
apart from `x * 0` has its factor apart from `0`), which constructive
axiomatisations of the reals take as an axiom for the same reason.

Each carrier proves it its own way:

- **`Rat`** decides `≤`, so the refutation is enough
  (`Rat::pos_of_mul_pos`, by `lt_of_not_le`), with no arithmetic beyond
  `mul_le_mono_r`.
- **`CReal`** builds the gap (`CReal::pos_of_mul_pos`). The product reads
  both factors at one index `a`. Past both gaps' starts, `x_a · y_a ≥
  1/(j+1)` and `x_a` lies in `(0, l+1]`, `l` the canonical bound of `x`,
  so `y_a ≥ 1/((l+1)(j+1))` (`Rat::le_of_mul_le_bounded`). That is a
  single term, and `a` is chosen far enough out (`16m + 15`, `m` the new
  gap's index) for `lt_of_term` to turn one term into a gap.

Derived once, at both carriers:

| Theorem | Statement | From |
|---|---|---|
| `inv_pos` | `0 < x` gives `0 < x⁻¹` | `x · x⁻¹ ≈ 1 > 0`, reflected by `x` |
| `inv_neg` | `x < 0` gives `x⁻¹ < 0` | `(-x) · (-x⁻¹) ≈ 1`, reflected by `-x` |
| `inv_inv` | `(x⁻¹)⁻¹ ≈ x` | `inv_unique` |
| `inv_lt_inv` | `0 < x < y` gives `y⁻¹ < x⁻¹` | `x < y` times the positive `x⁻¹ · y⁻¹` |
| `archimedean_inv` | `0 < x` gives some `1/(n+1) < x` | `x⁻¹` is below some `of_nat(n) < of_nat(n+1)`; invert |

Each theorem takes the apartness proofs it inverts at explicitly, so it
applies whatever proof a client's `x⁻¹` found; `inv_respects` makes the
choice immaterial. `archimedean_inv` states its `1/(n+1)` as
`inv(of_nat(n+1))` at the proof `of_nat_pos` gives. At `CReal` the client
writes it as `CReal::ofRat(Rat::ofInt(OfNat(Succ(n))))⁻¹`, with the
apartness searched, and the two inverses are convertible.

At a call site with `x⁻¹` notation the searched apartness of each inverted
point must be findable, so `docs/showcase/ordered_field_client.hthr`'s
`creal_inv_lt_inv` takes `0 < y` as a hypothesis, even though the generic
theorem derives it from `0 < x < y`.

## Calling a generic theorem

A generic theorem's indices are filled from its carrier, and the carrier is
read off an explicit point (or a type argument, `le_of_lt<Rat>(x, y, h)`), so
every generic theorem takes its points explicitly:
`StrictOrder::le_antisymm(x, y, hxy, hyx)`, not `(hxy, hyx)`. With implicit
endpoints, the hypothesis `?lt(?x, ?y)` is not a pattern the unifier can solve
against `Rat::Lt(a, b)` before the carrier is known.

A predicate meets its own unfolding: a `Close(x, y, e)` hypothesis passes
where `AbsLt(x - y, e)` is expected, and a result `AbsLt(x, e)` checks against
`-e < x ∧ x < e` at a carrier. The unifier learns nothing from two different
predicates' argument lists, the carrier's designations fill the indices, and
conversion does the unfolding
([constrained-predicate-expected-type](../issues/constrained-predicate-expected-type.md)).

## Cost

The module elaborates in a few seconds; every proof is a short chain of
dictionary laws. The reflection law costs `Rat` two lemmas
(`pos_of_mul_pos`, `le_of_mul_le_bounded`) and `CReal` one. The instances cost the carriers one lemma each at `Rat`
(`not_lt_of_le`, `zero_lt_one`) and three at `CReal` (`archimedean`,
`zero_lt_one`, `ofNat_succ`). `rat` now imports `ordered_field`, so `rat`,
`creal` and their clients re-elaborate once.
