# Ordered algebra: order meeting `+` and `*` below the field

Issue: `issues/ordered-algebra-api.md`. Module: `lib/std/algebra/ordered_field.hthr`
(the classes and the `Nat`/`Int` instances), `lib/std/num/float/dyadic.hthr` (the
`Dyadic` instance). Builds on `docs/constructive-ordered-field-design.md`, which
designed the field's layers. This note covers what sits below them.

## 1. What the issue asked, and what had happened since

The issue (filed 2026-09-02) asked for the compatibility laws between order and
algebra to be factored, without choosing one large `OrderedRing` up front. It
asked which compatibility theories `Nat`, `Int`, the rationals, absolute value and
interval reasoning each consume, and it asked that the strict and non-strict
distinction be kept constructive.

By 2026-11-02 the field half existed: `StrictOrder` → `PseudoOrder` →
`OrderedAddGroup` → `LocatedAddGroup` → `OrderedField`, with `Rat` and `CReal` as
instances. Nothing below the field connected order to `+` and `*`. Three things
showed the gap:

- `Nat` and `Int` had no ordered-algebra instance. `big_operator.hthr` carried
  `Nat::range_le` and `Int::range_le` as hand copies of
  `LocatedAddGroup::range_le`. Each carrier kept its own `add_le_mono`,
  `mul_le_mono_l`, `mul_nonneg` and `sq_nonneg`.
- The multiplication theorems (`mul_le_mono_*`, `mul_nonneg`, `sq_nonneg`,
  `mul_le_mul`, `neg_of_mul_neg`, `pos_of_mul_pos_nonneg`) lived at
  `OrderedField`, though only one of them used the reciprocal, and that one did not
  need it. `Int` and `Dyadic`, which are rings but not fields, could not reach
  them.
- `Dyadic` had a `CommRing` and a `PseudoOrder` but nothing joining the two.

## 2. Decisions

**One hierarchy, strict-first.** The lower layers extend the same
`StrictOrder(≈, <, ≤)` the field layers use. There is no second, `≤`-only
hierarchy for the decidable carriers. `Nat` and `Int` fill `StrictOrder` without
cost, since their `≤` is `¬(y < x)` by a decision. This is option B of
`issues/strict-order-presentation.md` (two relations and their agreement), which
`StrictOrder` already was. That issue stays open for its notation questions.

**The laws are the monotone forms, and the signs are theorems.** A semiring with
no subtraction cannot derive monotonicity from `mul_pos`, because `y = x + d`
has no `d` in general. So the semiring's laws are those a positive factor obeys:

```
OrderedAddMonoid:  add_lt_mono_r   x < y → x + z < y + z
                   add_lt_reflect_r x + z < y + z → x < y
OrderedSemiring:   zero_lt_one     0 < 1
                   mul_lt_l        x < y → 0 < z → z·x < z·y
                   mul_lt_reflect_l 0 < z → z·x < z·y → x < y
```

In a group the additive reflection follows by adding the inverse, but a monoid has
no inverse to add, so it is a law. The multiplicative reflection is strong
extensionality of `*` at a positive factor. That is a constructive law of its
own, the same one the field's `pos_of_mul_pos` field stated. `mul_pos`,
`pos_of_mul_pos`, `neg_of_mul_neg`, `mul_nonneg` and `mul_le_mul` are all theorems
of the semiring now. `OrderedField` lost its `zero_lt_one`, `mul_pos` and
`pos_of_mul_pos` fields to `OrderedSemiring`. The laws are named apart from the
theorems (`mul_lt_l` beside `OrderedSemiring::mul_lt_mono_l`), because a theorem
named like a field makes every `A.field` call ambiguous.

**`≤` monotonicity by a nonnegative factor needs no locatedness and no
subtraction.** Suppose `x ≤ y`, `0 ≤ z` and `z·y < z·x`. If `z` were positive,
reflection would give `y < x`. So `z` is not positive. It is not negative either,
since `0 ≤ z`, so by tightness `z ≈ 0`. Then both products are `≈ 0`, and the gap
between them is refuted. Because the goal is a refutation, nothing is decided
(`OrderedSemiring::mul_le_mono_l`). The field's old proof went through a
subtraction and `pos_of_mul_pos_nonneg`. That theorem still exists, at the
semiring, proved by cotransitivity with no negation: either `(z+1)·d` is
positive, or `z·d + d < z·d` puts `d` below zero and then `z·d ≤ z·0`.

**Locatedness sits under the multiplication layers.** `OrderedSemiring` extends
`LocatedAddMonoid`, and `OrderedRing` extends `LocatedAddGroup`. Every carrier
here is located, and `mul_le_mul` needs `≤` transitivity. An unlocated semiring
has no consumer, and the unlocated/located split stays where the field design put
it: at the order and the additive group. The commutative semiring is the only
semiring. No noncommutative ordered carrier exists to ask for less.

**`OrderedRing` has no fields of its own.** It is the semiring and the located
group together. What negation adds is theorems: a square's sign
(`OrderedRing::sq_nonneg`) and nonpositive factors (`mul_le_mono_*_nonpos`).
`OrderedField` extends it and keeps only what needs the field: `recip`,
`mul_recip`, `of_nat` with its two laws, and `archimedean`.

**Archimedean and `of_nat` stay at the field.** `Int`, `Dyadic` and `Nat` are
Archimedean too, but no consumer below the field asks for the property, so it is
not a capability of its own yet. When an interval or analysis theorem over an
ordered ring needs it, the shape is the same as `Cotransitive`: a separate class
beside the ring.

**Instances live with the class or with the carrier, whichever is imported
later.** `ordered_field` imports `nat` and `int`, so the `Nat` and `Int`
instances sit at the end of `ordered_field.hthr`, as `semiring.hthr` hosts their
ring instances. `Dyadic` imports `ordered_field`, so its instance sits in
`dyadic.hthr`. Facts the instances need are in their type's file:
`Nat::mul_lt_mono_l`, `Nat::lt_of_mul_lt_mul_l`, `Int::mul_lt_mono_l`,
`Int::lt_of_mul_lt_mul_l`, `Rat::lt_of_mul_lt_mul_l` and
`CReal::lt_of_mul_lt_mul_l`. The linear fields are `omega`.

## 3. What each carrier fills

| Carrier | Layer | Notes |
| --- | --- | --- |
| `Nat` | `OrderedSemiring` | at `RelId`; no group, so the monoid layers are its home |
| `Int` | `OrderedRing` | at `RelId` |
| `Dyadic` | `OrderedRing` | laws read off `Rat` through `.rat()`; no reciprocal |
| `Rat`, `CReal` | `OrderedField` | parents synthesized from the field's instance |
| `Finite(F)` | `PseudoOrder` | float values; no exact arithmetic, so no algebra layer |

## 4. Names moved

Each theorem took the name of the weakest class it needs, which is the existing
convention (`StrictOrder::le_antisymm`, `PseudoOrder::le_trans`). Call sites were
renamed mechanically:

- `OrderedAddGroup::{add_respects, add_lt_mono(_l), add_lt_cancel_{l,r},
  add_le_mono_{l,r}, add_pos}` → `OrderedAddMonoid::…`
- `LocatedAddGroup::{add_lt_cancel, pos_of_add_pos, add_le_mono, add_lt_le_mono,
  add_le_lt_mono, add_nonneg, range_le, range_nonneg}` → `LocatedAddMonoid::…`
- `OrderedField::{mul_respects, one_apart_zero, mul_lt_mono_{l,r},
  mul_le_mono_{l,r}, mul_nonneg, mul_le_mul, neg_of_mul_neg,
  pos_of_mul_pos_nonneg}` → `OrderedSemiring::…`;
  `OrderedField::mul_pos_of_pos` and the field `A.mul_pos` →
  `OrderedSemiring::mul_pos`; the field `A.pos_of_mul_pos` →
  `OrderedSemiring::pos_of_mul_pos`
- `OrderedField::{mul_le_mono_{l,r}_nonpos, sq_nonneg}` → `OrderedRing::…`

`mono`'s class table (`lib/std/tactic/mono.hthr`, `mono_classes`) has a row for
each new class. A goal inside `section<A: OrderedSemiring(…)>` gets the semiring's
laws, and one inside `section<A: OrderedAddMonoid(…)>` gets translation.
`Nat::range_le` and `Int::range_le` remain as named one-line calls to the generic
theorem, because `mono`'s carrier tables cite them.

## 5. Not done here

- **`npow` below the field.** `OrderedField::npow` (in `real_fn.hthr`) is
  `∏ j < n, x`, which a semiring has. Its monotonicity and sign belong at
  `OrderedSemiring` once a consumer below the field asks. `Nat::pow`,
  `Rat::npow` and `CReal::npow` are separate fixpoints, so a generic one would
  meet them through coincidence lemmas.
- **`linarith` at an ordered ring.** It needs rational coefficients, so it stays
  at `OrderedField`. At `Int` and `Nat` it already runs through the integral
  reading.
- **Interval theorems at an ordered ring.** `Interval::HasIn` is generic over
  `OrderedField` plus a morphism from `Rat`. Containment for `+`, `-` and `*`
  needs only a ring, so a `Dyadic`-endpoint reading could drop to `OrderedRing`.
  Division is what keeps it at the field.
- **A failing `mono` at a field costs memory.** Its product laws now upcast the
  section's `OrderedField` dictionary to `OrderedSemiring`, and every subgoal
  carries the upcast record. A successful search costs what it did. A failing one
  peaks at a few GB (`issues/mono-failure-under-upcast-cost.md`), so `mono`'s
  refusal probes sit in an `OrderedSemiring` section.
- **Lattices** landed separately (`docs/lattice-structure-design.md`).
  **Trichotomy** (`issues/trichotomy-proposition.md`) is adjacent and unchanged.

## 6. Cancellation

Issue: `issues/cancellative-algebra-api.md`. The issue asked for an API that keeps
an unconditionally cancellative operation apart from the integral-domain-shaped
step that cancels a nonzero factor. The forcing customer was transitivity of
cross-multiplication for unreduced rationals with positive denominators.

**The distinction is carried by hypotheses, not by a class.** Unconditional
cancellation has no side condition in its statement, and conditional
cancellation names its condition:

| Theorem | Layer | Side condition |
| --- | --- | --- |
| `OrderedAddMonoid::add_cancel_{l,r}`, `add_le_cancel_{l,r}` | ordered additive monoid | none |
| `OrderedSemiring::mul_cancel_pos_{l,r}`, `mul_le_cancel_pos_{l,r}` | ordered semiring | `0 < z` |
| `OrderedRing::mul_cancel_apart_{l,r}` | ordered ring | `ApartBy(<, z, 0)` |
| `Nat::mul_cancel_{l,r}`, `Int::mul_cancel_{l,r}` | the carrier | `¬(z = 0)` |

Additive cancellation is a theorem of every ordered additive monoid, because a
gap between the summands survives translation and contradicts the equation. It
is a theorem of every group as well. Together these two cover every carrier
here, so a `Cancellative(≈, op)` class has no consumer yet and was not added.
The first carrier that is neither ordered nor a group (`List` under `++`) would
be the one to ask for it.

Multiplicative cancellation follows from the reflection law `mul_lt_reflect_l`
and tightness, so it needs no field. A gap between `x` and `y` would scale to a
gap between `z·x` and `z·y`. At a ring the condition weakens to apartness from
zero, the constructive "nonzero": a negative factor is a positive one negated.
`¬(z ≈ 0)` is not offered at the generic layers, because the reals cannot turn
it into a sign. At `Nat` and `Int` the decision makes `≠ 0` and apartness
agree, so their `≠ 0` forms are carrier theorems in `nat.hthr` and `int.hthr`,
proved from the carriers' own lemmas.

**The customer.** `OrderedSemiring::cross_same_trans` says that `a·d ≈ c·b` and
`c·f ≈ e·d` give `a·f ≈ e·b` once `d` is positive. `Rat::same_trans` is that
theorem at `Int`. It replaced a `ring` call followed by
`Int::mul_cancel_pos_r`.
