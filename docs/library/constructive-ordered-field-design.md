# The constructive ordered-field interface

For [constructive-ordered-field-interface](../../issues/constructive-ordered-field-interface.md).
The module is `lib/std/algebra/ordered_field.hthr`; its instances are at the end of
`lib/std/num/rat.hthr` and `lib/std/num/creal.hthr`; the client is
`docs/showcase/ordered_field_client.hthr`, checked with the controls in
`crates/elab/tests/lib_std_ordered_field.rs`.

## What both carriers share

The two carriers were written before the interface, and the interface is
what they turned out to have in common
([regular-cauchy-reals-round](creal.md), "What the
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
Zero, one, negation, the reciprocal and the embedding of `Nat` are fields,
as `Group`'s inverse is. The algebra is not restated: the additive group is
`algebra_rel`'s `GroupRel` and the field's ring is `semiring`'s `CommRing`
(see "Built on the ring layers" below).

| Layer | Adds | What first needs it |
|---|---|---|
| `StrictOrder(≈, <, ≤)` | `Equivalence(≈)`; `<` irreflexive, transitive, respecting `≈`, tight; `≤` ⇔ `¬>` | open intervals, apartness laws, `≤` reflexive and antisymmetric modulo `≈` |
| `Cotransitive(<)` | `x < y → x < z ∨ z < y` | (a capability, alone) |
| `PseudoOrder` | the two above | `≤` transitivity, mixed `<`/`≤` steps, closed intervals, apartness cotransitivity |
| `OrderedAddGroup(≈, <, ≤, +)` | `StrictOrder`, `algebra_rel`'s `GroupRel`/`Commutative` at `+` (zero `unit`, negation `inv`), `<` translation-invariant | group algebra, `≤` translation, the bounded triangle inequality, tightness of bounds |
| `LocatedAddGroup` | `OrderedAddGroup` and `PseudoOrder` | a sum's gap splitting between summands, a bound's positivity, `≤` bounds |
| `OrderedField(≈, <, ≤, +, *)` | `semiring`'s `CommRing` (one `multiplicative.unit`), `of_nat`, the reciprocal `recip` at apartness, `0 < 1`, `mul_pos`, `pos_of_mul_pos`, Archimedean | strict monotonicity of products, uniqueness and invariance of the reciprocal |

> **Since 2026-11-02** (`docs/library/ordered-algebra-design.md`): `0 < 1` and the products' laws moved down to `OrderedSemiring`, in their monotone forms (a positive factor keeps and reflects `<`), and `mul_pos`/`pos_of_mul_pos` are theorems there. `OrderedField` extends `OrderedRing` and keeps `recip`, `of_nat` and Archimedean. The table and the text below describe the field as first built.


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

## Built on the ring layers

For [ordered-field-over-comm-ring](../../issues/ordered-field-over-comm-ring.md).
The interface first restated the ring laws as fields of its own (`zero`,
`neg`, `add_zero`, `add_neg`, `one`, `mul_assoc`, `mul_comm`, `mul_one`,
`mul_add_distr`, `mul_respects`) and re-proved `Ring`'s sign lemmas, so a
`Ring` theorem did not apply to an `OrderedField` binder. Now:

- `OrderedAddGroup` extends `GroupRel(≈, +)` and `Commutative(≈, +)`,
  untagged. Zero is `A.unit`, negation `A.inv`; the group's own laws
  (`unit_l`, `inv_l`, `inv_respects`, …) replace the restated ones, and
  `GroupRel::inv_unique`/`inv_inv` and `CommMonoidRel::interchange` replace
  `neg_unique`, `neg_neg` and `add_add_add_comm`. The theorems about
  negation keep `neg` in their names (`neg_lt`, `neg_add`), as `Ring`'s
  `neg_mul` does.
- `OrderedField` extends `LocatedAddGroup` and `CommRing(≈, +, *)`. The
  additive group is reached twice, through the located group and through
  the ring, at the same untagged fiber, so it is one copy. One is
  `A.multiplicative.unit`; associativity and the unit laws of `*` are
  `A.multiplicative.*`, commutativity `A.commutative.comm`, distributivity
  `distrib_l`/`distrib_r`, and `Ring::mul_neg`, `neg_mul`, `neg_mul_neg` and
  the field `mul_zero` replace the re-proved copies. Congruence of `*` is
  `OrderedSemiring::mul_respects`, one projection of the tagged semigroup's
  `Respects2`.
- The field's reciprocal is `recip` (law `mul_recip`), because `inv` is the
  additive group's, inherited untagged; its theorems are `recip_unique`,
  `recip_pos`, … . At the carriers it is still `x⁻¹`.

The carriers register their `CommRing` before their ordered instances.
`Rat` had its ring already; `CReal` gains one from its existing lemmas plus
`one_mul`, `zero_mul` and `neg_add_self`, each its mirror read through
commutativity.

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

## The reciprocal, positivity and the Archimedean property

The reciprocal is `recip: (x: A) → ApartBy(<, x, unit) → A`, the same shape as
`x⁻¹` at both carriers (`x.inv(h := infer)` over `x.Apart(0)`); the
instances pass the proof through, and `refl` shows the field is the
carrier's own `x⁻¹`. `OrderedField::recip_unique` and `recip_respects` are
proved once from `mul_recip` and the ring laws, so the inverse is independent
of the apartness proof that built it at every carrier. `CReal` had
`inv_respects` already, proved through gaps; it gets `recip_unique` for free.

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

For [ordered-field-inverse-sign](../../issues/ordered-field-inverse-sign.md).
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
| `recip_pos` | `0 < x` gives `0 < x⁻¹` | `x · x⁻¹ ≈ 1 > 0`, reflected by `x` |
| `recip_neg` | `x < 0` gives `x⁻¹ < 0` | `(-x) · (-x⁻¹) ≈ 1`, reflected by `-x` |
| `recip_recip` | `(x⁻¹)⁻¹ ≈ x` | `recip_unique` |
| `recip_lt_recip` | `0 < x < y` gives `y⁻¹ < x⁻¹` | `x < y` times the positive `x⁻¹ · y⁻¹` |
| `archimedean_recip` | `0 < x` gives some `1/(n+1) < x` | `x⁻¹` is below some `of_nat(n) < of_nat(n+1)`; invert |

Each theorem takes the apartness proofs it inverts at explicitly, so it
applies whatever proof a client's `x⁻¹` found; `recip_respects` makes the
choice immaterial. `archimedean_recip` states its `1/(n+1)` as
`recip(of_nat(n+1))` at the proof `of_nat_pos` gives. At `CReal` the client
writes it as `CReal::ofRat(Rat::ofInt(OfNat(Succ(n))))⁻¹`, with the
apartness searched, and the two inverses are convertible.

At a call site with `x⁻¹` notation the searched apartness of each inverted
point must be findable, so `docs/showcase/ordered_field_client.hthr`'s
`creal_inv_lt_inv` takes `0 < y` as a hypothesis, even though the generic
theorem derives it from `0 < x < y`.

## Calling a generic theorem

A generic theorem's indices are filled from its carrier: from the section's
dictionary in scope, or from the carrier's designations. The carrier is read
off an explicit point, a type argument (`le_of_lt<Rat>(x, y, h)`), or, since
issues/generic-theorem-implicit-points.md, the **type of any solved slot**:
a hypothesis `h1: a < b` at an implicit-pointed theorem
(`p({x, y, z: K}, h1: x < y, h2: y < z)`) solves `?x := a` and `?< := <`, and
`a : Rat` (or the order's own type) is what solves `?K`. The call then reads
like the carrier's own, `p(h1, h2)`, inside a section and at `Rat` or
`CReal` alike, and a theorem with no point at all (`two_pos()`) is pinned by
its expected type. Hypotheses at two carriers are refused naming the point
only the second one mentions, as at a concrete carrier.

The library's theorems still take their points explicitly
(`StrictOrder::le_antisymm(x, y, hxy, hyx)`); moving them to implicit points
is issues/class-theorems-implicit-points.md, which also has to move `mono`'s
lemma table, whose calls are built positionally.

A predicate meets its own unfolding: a `Close(x, y, e)` hypothesis passes
where `AbsLt(x - y, e)` is expected, and a result `AbsLt(x, e)` checks against
`-e < x ∧ x < e` at a carrier. The unifier learns nothing from two different
predicates' argument lists, the carrier's designations fill the indices, and
conversion does the unfolding
([constrained-predicate-expected-type](../../issues/constrained-predicate-expected-type.md)).

## Cost

The module elaborates in a few seconds; every proof is a short chain of
dictionary laws. The reflection law costs `Rat` two lemmas
(`pos_of_mul_pos`, `le_of_mul_le_bounded`) and `CReal` one. The instances cost the carriers one lemma each at `Rat`
(`not_lt_of_le`, `zero_lt_one`) and three at `CReal` (`archimedean`,
`zero_lt_one`, `ofNat_succ`). `rat` now imports `ordered_field`, so `rat`,
`creal` and their clients re-elaborate once.
