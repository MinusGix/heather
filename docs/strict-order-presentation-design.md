# Strict order presentation: which relations an order class takes

Issue: `issues/strict-order-presentation.md` (closed by this note). Module:
`lib/std/algebra/ordered_field.hthr` (`StrictOrder`, `PseudoOrder`),
`lib/std/algebra/order.hthr` (`Preorder`, `PartialOrder`, `LinearOrder`).
Builds on `docs/ordered-algebra-design.md` and
`docs/constructive-ordered-field-design.md`.

## 1. The question, and what had happened since it was filed

The issue (2026-08-09) asked whether an order class takes one relation and
derives its strict notation (option A, `Preorder<A>(le)` plus a notation
expression for `<`), or takes both relations with their agreement as a law
(option B, `Preorder<A>(le, lt)`). Its 2026-08-16 log leaned to B, with a
target hierarchy `Preorder<A>(le, lt) → PartialOrder → LinearOrder`.

By 2026-11-02 the library had two order families, and neither was that target:

- **The non-strict family** (`order.hthr`, from `mathematical-order-hierarchy`):
  `Preorder(R)`, `PartialOrder(R)` and `LinearOrder(R)`, one relation each.
  Products and injective pullbacks are its constructions. `Nat` and `Int`
  register `LinearOrder(Le)`.
- **The strict-first family** (`ordered_field.hthr`): `StrictOrder(≈, <, ≤)`,
  then `PseudoOrder`, then the ordered-algebra layers up to `OrderedField`. It
  takes both relations as indices, and its laws say how they agree. `Nat`,
  `Int`, `Dyadic`, `Rat` and `CReal` all fill it.

Two things showed that the presentation question was still open in practice.

**Generic `calc` refused `<` and `≤`.** `calc` folds a chain through
`Transitive(R)` and `Trans(R, S, T)` instances (`docs/calc-order-chains.md`).
Inside `section<A: PseudoOrder(≈, <, <=)>` the only one in scope was
`Transitive(≈)`, which comes from the `Equivalence` parent. A chain
`x < y, < z` was refused with "no instance for `Transitive<A>(R)`", and
`x < y, <= z` with "`Trans` has no instances". So generic order proofs were
written as nested calls, with every endpoint spelled out:

```heather
PseudoOrder::lt_of_lt_of_le(x + y, x2 + y, x2 + y2, A.add_lt_mono_r(x, x2, y, hx), OrderedAddMonoid::add_le_mono_l(y, y2, x2, hy))
```

**Every carrier copied the same instances.** `Rat`, `CReal`, `Dyadic` and
`Finite(F)` each declared `Preorder(Le)`, `Transitive(Lt)` and six `Trans`
pairs. All eight follow from the carrier's `PseudoOrder` instance, and only
the concrete carrier could use them.

## 2. Decisions

### 2.1 Each family takes the relation that is primitive in it

**Linear orders that meet algebra are presented strict-first, with both
relations as indices.** `StrictOrder(≈, <, ≤)` is option B. Its agreement is
not the issue's sketch `lt ↔ le ∧ ¬ge`, though. It is Bishop's `x ≤ y ↔
¬(y < x)` (`le_of_not_lt`, `not_lt_of_le`), which defines `≤` from `<` rather
than `<` from `≤`. Together with `lt_tight`, it makes the family the
constructive *linear* orders. Two points neither of which is below the other
are `≈`, so incomparable points cannot exist. The `<` is positive data (a gap
at the reals), and the `≤` is the carrier's own spelling, kept as an index so
that `Rat`'s cross-multiplied `≤` and `Nat`'s computing `Le` are used directly.

**Orders that need not be linear keep one relation.** `Preorder(R)` and
`PartialOrder(R)` do not grow an `lt` index. If a strict relation is wanted
over such an order, it is one of two things:

- the strict part, `R(x, y) ∧ ¬R(y, x)`. That is a definition over `R`, to be
  written when a consumer asks for it. It is not a class index.
- an independent relation, such as componentwise `<` on a product. That is
  another indexed relation, as the issue's boundaries already say.

**Why this reverses the 2026-08-16 target `Preorder<A>(le, lt)`.** Each of
the three reasons recorded there is served by the strict-first family, and
none needs B inside `Preorder`:

1. *`Nat`'s `Lt` computes.* It is the `<` index of
   `StrictOrder<Nat>(RelId<Nat>, Nat::Lt, Nat::Le)`, so it is used as is.
2. *Products and lexicographic orders relate `<` and `≤` differently.* B's
   agreement `lt ↔ le ∧ ¬ge` would force `lt` to be the strict part anyway,
   so B would not admit componentwise strictness. For `product_preorder`, B
   would only add a second relation and a proof that it is the strict part,
   which no consumer reads. Ordinals, which want `<` primitive, are
   strict-first.
3. *Well-founded recursion is stated on `<`.* In the strict-first family,
   `<` is an index, not notation for a derived relation.

**`LinearOrder(≤)` stays.** Its totality, `x ≤ y ∨ y ≤ x`, is a decision at
`Nat` and `Int` and is false constructively at `CReal`, where a pseudo-order
has only `¬¬`-totality. The decidable carriers register both
`LinearOrder(Le)` and the strict-first layers. They meet in `≤`: since
`PseudoOrder` presents `Preorder(≤)` (§2.2), `Nat`'s and `Int`'s
strict-first instances use the `Preorder` that `LinearOrder` synthesized.

### 2.2 The presentation includes what the two relations are as relations

A strict order's `<` is a `Transitive` relation, and `≈` chains with `<` and
with `≤` on either side. A located one also has `≤` as a `Preorder` and the
mixed `<`/`≤` steps. The classes say so as **tagged parents**:

```heather
class StrictOrder<A>(same as ≈: …, lt as <: …, le as <=: …)
    extends Equivalence<A>(same), Transitive<A>(lt) as lt_transitive,
        Trans<A>(same, lt, lt) as same_lt, Trans<A>(lt, same, lt) as lt_same,
        Trans<A>(same, le, le) as same_le, Trans<A>(le, same, le) as le_same
{ … }

class PseudoOrder<A>(same as ≈: …, lt as <: …, le as <=: …)
    extends StrictOrder<A>(same, lt, le), Cotransitive<A>(lt), Preorder<A>(le) as le_preorder,
        Trans<A>(lt, le, lt) as lt_le, Trans<A>(le, lt, lt) as le_lt
{}
```

They are tagged because untagged parents would flatten `Transitive` at two
fibers into one dictionary. `Equivalence(≈)` already brings
`Transitive(≈)`, and the class declaration refuses a second one ("inherits
the class `Transitive` at two distinct fibers"). Each view sits at the
weakest class where it holds. The `≈` transports need only `lt_respects` and
`StrictOrder::le_respects`. `≤`'s transitivity and the mixed pairs need
cotransitivity (`PseudoOrder::le_trans`, `lt_of_lt_of_le`), so they sit at
`PseudoOrder`.

Resolution finds a tagged parent of a section's dictionary, so a generic
`calc` now steps through `<`, `≈` and `≤`:

```heather
section<A: PseudoOrder(≈, <, <=)> {
theorem located_chain(v, w, x, y, z: A, h1: v <= w, h2: w <= x, h3: x < y, h4: y ≈ z): v < z {
    calc { v <= w := h1, <= x := h2, < y := h3, ≈ z := h4, }
}
}
```

Six theorems in `ordered_field.hthr` are rewritten as chains to show it:
`OrderedAddMonoid::add_lt_mono` and `add_pos`, and `LocatedAddMonoid::add_le_mono`,
`add_lt_le_mono`, `add_le_lt_mono` and `add_nonneg`.

**Where the views come from today.** An instance fills a tagged parent from an
already-registered canonical instance at its carrier
(`docs/traits-layer1-design.md` §4.3, rule 3, fill-by-reference). This is how
each carrier gets them:

| Carrier | Source of the views |
| --- | --- |
| `Rat`, `CReal`, `Dyadic` | their existing hand instances, by reference; no instance changed |
| `Nat`, `Int` | `Transitive(Lt)`, the two `<`/`≤` pairs and `LinearOrder`'s `Preorder(Le)`, by reference, plus four new `RelId` transports each (`order.hthr`) |
| `Finite(F)` | written as fields of its `StrictOrder` and `PseudoOrder` instances, because a parameterized instance offers no fill-by-reference |

**The views follow from the class's own fields.** They are per-carrier only
because a class cannot yet fill an inherited field from its own fields. That
is `issues/class-inherited-field-implementations.md`, and this is its first
order consumer. With it, `StrictOrder` would write `lt_transitive :=
Transitive(lt_trans)` once. The hand instances at five carriers and
`Finite(F)`'s literal fields would then all go.

**Imports.** A section's dictionary type now mentions `Preorder`, and a
class's parents are named in the client's scope. So every module that opens a
section over `PseudoOrder` or a class above it imports `order`, as all of them
already import `relation_props` for `Equivalence`. Sixteen modules gained the
line. Without it, the refusal is "`Preorder` takes no type arguments", at the
end of the module.

### 2.3 Notation

Both relations are indices, so nothing needs option A's derived-notation
expressions. `<` and `≤` are bound by the index binders' `as` symbols, as `+`
is. What is left belongs to `issues/class-default-operators.md`, and this
issue asks one thing of it: `(≈, <, ≤)` is one package. Today no collision
can arise, because every binder spells all three symbols
(`section<A: PseudoOrder(≈, <, <=)>`). Once classes advertise defaults,
`StrictOrder` advertises the triple, and a binder that overrides one symbol
overrides the package. Domain spellings such as `≽`/`≻` are aliases, and
`issues/class-alias-roles.md` owns them.

## 3. Not done here

- **The strict part of a preorder** (`StrictPart(R)` and its irreflexivity,
  transitivity and the two `Trans` pairs with `R`). No consumer asks for it.
- **`PartialOrder(≤)` from a strict-first order at `RelId`.** Antisymmetry
  at `=` holds when `≈` is identity, but a class cannot say "when the setoid
  is `RelId`". `Nat` and `Int` already register `LinearOrder`, so nothing is
  missing at a carrier.
- **Retiring the per-carrier views.** That waits on
  `issues/class-inherited-field-implementations.md`.
- **A class parent named outside the client's imports.** This is the import
  rule in §2.2. The `RelId` gotcha in the ordered-algebra round (an instance
  head that names `RelId<Nat>` needs `import relation`) is the same thing.
  Filed as `issues/class-parent-names-resolve-in-client-scope.md`.
