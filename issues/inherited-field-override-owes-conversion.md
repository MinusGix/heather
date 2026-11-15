---
title: Repeating an inherited class field in a sub-class instance owes a conversion between two proofs
status: open
labels: [traits,design,proofs]
area: language
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]), which added `algebra`'s `Group`
and its first instance. Not a blocker — the working spelling is one line shorter
than the failing one — but a design line worth having written down, because the
rule that produces it is right and its consequence is surprising.

`Int` already has `CommMonoid<Int>(add)` as its canonical monoid. Writing the
group instance with the inherited fields repeated:

```heather
instance Group<Int>(add) {
    unit := OfNat(0), assoc := add_assoc, unit_l := zero_add, unit_r := add_zero,
    inv := neg, inv_l := neg_add_self, inv_r := add_neg,
}
```

is refused: "overrides `unit_r`, which the canonical `Monoid` at `Int` already
holds, and the two are not convertible: an override owes agreement
(`docs/language/classes/traits-layer1-design.md` §4.5)". The canonical instance holds
`λ (x: Int) => refl`; this one holds `add_zero`, an opaque `theorem`. Both prove
`add(x, OfNat(0)) = x` and neither reduces to the other, because **Heather is
proof-relevant**: two proofs of one equation are not convertible in general, and
`theorem` opacity means even two `refl`-shaped proofs are not, once one of them
has a name.

So §4.5's rule — an override owes agreement — is satisfiable at a *program* field
(`unit := OfNat(0)` converts fine) and generally **unsatisfiable at a proof
field**, unless the writer copies the canonical instance's term verbatim.

Two smaller things found on the way, both real:

- Copying the term verbatim does not work either: `unit_r := λ (x: Int) => refl`
  in the override position fails with "`refl` needs an expected type (checking
  position or `as` motive)", so the agreement check elaborates the override
  without the field's type in hand. That is a plain defect inside the rule, and
  it is what makes "copy the canonical term" not a workaround.
- The **working** spelling is to omit every inherited field and write only the
  three new ones, which is what `lib/std/num/int.hthr` does. It reads better than the
  repetition, so nothing was lost here — but a writer's first instinct is to fill
  in what the class body lists.

## What to decide

Either (a) proof fields are exempt from override agreement — an instance may not
disagree about a *program*, and two proofs of the same statement are
interchangeable by fiat at the class boundary; or (b) overriding an inherited
field is refused outright with a message that says "omit it; the canonical parent
holds it", which is a one-line diagnostic change and matches what a writer should
do anyway. (b) is smaller and loses nothing this round could see.

Independent of the choice, the "`refl` needs an expected type" leak should go: the
agreement check has the field's type and should check the override against it.

## What it assumes from elsewhere

- **[[std-int-encoding]]** owns `Group`'s existence and `Int`'s instance. Assumed
  here: only that `Int` is a group under `add` and that its monoid structure is
  already registered by a *different* instance.
- **[[class-ops-prop-vs-bool]]** owns proof relevance in class fields. Assumed
  here: only that a law field holds a proof term rather than a decision.

## Log

- 2026-08-17: Filed by the `Int` round while adding `Group` to `lib/std/algebra/algebra.hthr`. Ranked #4 of six: it cost minutes, not lines, and the working spelling is the nicer one.
