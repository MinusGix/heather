---
title: Decide how order classes present strict and non-strict relations
status: closed
labels: [design,traits,notation,stdlib,orders]
area: mathematics
milestone: [math-classes]
created: 2026-08-09
updated: 2026-11-02
---

Direction issue from the operation-indexed order discussion. An order library
wants paired notation such as `<=`/`<`, `>=`/`>`, `⊑`/`⊏`, or `≽`/`≻`, while
an operation-indexed class must say what mathematical function each symbol
means. The design has two honest centers and no decision yet:

1. `Preorder<A>(le)` takes one relation; strict notation expands to the
   canonical strict part derived from `le`.
2. `Preorder<A>(le, lt)` takes both relations; the dictionary carries their
   agreement as part of what a preorder presentation means.

Do not introduce a separate `PresentedOrder` companion merely to house the
second choice. If independently supplied strictness is the normal abstraction,
`Preorder` itself should say so.

## Option A: one relation, derived strict notation

```heather
class Preorder<A>(le: A -> A -> Prop) {
    refl: ...,
    trans: ...,

    // Declaration-level notation sketch, not settled syntax:
    notation x < y := le(x, y) and not le(y, x),
}
```

The class advertises both its non-strict symbol and an explicit notation
expression for the strict relation. A domain alias can replace the spellings:

```heather
alias class PreferenceOrder<A> =
    Preorder<A>(prefers as ≽, strict as ≻)
```

The alias does not ask the lexer to infer that `≻` is the strict relative of
`≽`; it explicitly installs the pair. Unicode resemblance has no semantic
force.

Advantages:

- one mathematical relation identifies the preorder;
- no redundant coherence field;
- generic theorems get a canonical meaning of strictness;
- under the Prop/Compile separation, the derived specification can receive a
  specialized Compile instance, so runtime efficiency alone need not put a
  second predicate in the mathematical class.

Costs/questions:

- some domains regard both strict and non-strict relations as primitive
  vocabulary;
- the notation expression needs a clean declaration mechanism and access to
  negation/conjunction at the proposition layer;
- a separately optimized or independently defined strict predicate must be
  related to the derived one somewhere if clients want to name it directly.

## Option B: two relations in `Preorder`

```heather
class Preorder<A>(
    le: A -> A -> Prop,
    lt: A -> A -> Prop,
) {
    refl: ...,
    trans: ...,
    lt_iff: (x, y: A) -> lt(x, y) = (le(x, y) and not le(y, x)),
}
```

The exact agreement statement may use logical equivalence rather than identity;
the sketch records the obligation, not its final type.

Advantages:

- both natural predicates are directly nameable, indexable, and compilable;
- notation is a direct alias for supplied operations rather than an expression;
- domain libraries may use representations suited to each predicate.

Costs/questions:

- every preorder now carries a second relation and a coherence proof;
- generic calls and instance keys have another value index to infer or spell;
- independently supplied predicates create more ways for two nominally similar
  order instances to differ;
- the agreement field may be bureaucracy when strictness is never used.

## Notation installation and collisions

Whichever option wins, a class default or alias installs a **notation package**,
not isolated symbols with silent replacement. Installing two preorders whose
packages both claim `>`/`<` must not quietly clear or shadow the first.

The safe baseline is a named collision at the constraint binder:

```heather
A: NumericOrder + PreferenceOrder
```

If both advertise `>`, elaboration refuses and asks for an explicit symbol
override or for one default package to be disabled. This is useful pressure:
multiple order structures should normally receive distinct notation. Any
explicit replacement syntax must replace the requested class/alias's package
as a unit, so overriding `<=` cannot accidentally leave `<` referring to the
old relation.

Open alternatives for explicit control include `without notation`, a
per-constraint symbol list, or an alias that advertises the desired pair. The
issue owns the semantics before syntax is chosen.

## Boundaries

- No programmatic detection of "natural operator variations" from Unicode
  subscripts, superscripts, or visually related glyphs. Libraries may provide
  conventions, but declarations state the relationship.
- No extra companion order class solely to distinguish presentation choices.
- A strict relation that is mathematically independent rather than the strict
  part of a preorder is simply another indexed relation/class; this issue does
  not force it into order notation.
- Lattice presentations may take `le`, `meet`, and `join` together and carry
  compatibility laws, but that multi-operation design is adjacent rather than
  owned here.

## What it assumes from elsewhere

- **[[class-default-operators]]** owns how a class advertises default symbols
  and how binders install them. This issue supplies its main paired-operator
  customer and requires collision handling at package granularity.
- **[[class-alias-roles]]** owns domain aliases such as `PreferenceOrder` and
  `RefinementOrder`; assumed here only as a place to advertise alternate
  order-symbol pairs.
- **[[class-ops-prop-vs-bool]]** owns the choice to state mathematical
  relations in Prop/SProp and supply execution separately. Its current lean
  weakens the efficiency argument for storing a second strict predicate.
- **[[notation-extensibility]]** owns which relation symbols the lexer admits;
  this issue only assigns meanings to already parsed symbols.

## Log

- 2026-08-09: Filed with the design deliberately open between a one-relation
  preorder with declared derived strict notation and a two-relation Preorder
  carrying agreement. Rejected as directions: a separate `PresentedOrder`
  companion, Unicode-shape inference, and silently clearing an already
  installed `>`/`<` meaning.

## Log

- 2026-08-16: **Direction: Option B (two relations), from the std-API design discussion.** The user's lean, and mine: the class carries `le` and `lt` with their agreement as a defaulted field (`lt_iff_le_not_le`), rather than deriving strict notation from `le`. Three reasons, in increasing force. (1) At `Nat`, `Lt(n, m) := Le(Succ n, m)` **computes**, where the canonical strict part `le(x,y) /\ ~le(y,x)` does not, and the `le /\ x ≠ y` spelling needs decidable equality merely to be usable. (2) Different carriers relate the two differently — product and lexicographic orders derive `<` in ways that are not the canonical strict part of their `<=`, and ordinals want `<` primitive; a class that fixes the derivation forecloses those. (3) Well-founded recursion is stated on `<`, so making it notation for a derived thing means every termination argument unfolds a definition to reach its induction principle. Target hierarchy: `Preorder<A>(le, lt)` -> `PartialOrder` (antisymmetry) -> `LinearOrder` (totality + a decider), with `OrderedAddCommMonoid`/`OrderedSemiring` separately tying `+`/`*` to `<=` — that connection is what makes `add_le_mono`/`mul_le_mono` generic rather than `Nat`-specific, and it is where the existing `CommMonoid<Nat>(add)`/`(mul)` instances finally pay off. **One question this discussion dissolved rather than answered:** whether the order class should present a three-way `compare`/`Ordering` instead of two relations. Under the Prop-first direction ([[class-ops-prop-vs-bool]], same date) it is not a spec question at all — trichotomy is the mathematical content, and `Ordering` is a *representation of a decision procedure*, so it belongs on the compiled side with the rest of the downgrade. Not closing: this issue owns the class shape, and nothing has been written yet. `Nat`'s own `Lt` — which does not exist today — is owned by [[nat-order-kit]].
- 2026-08-16: 2026-08-16: Nat's Lt now EXISTS, which is the one thing this issue assumed from [[nat-order-kit]] (docs/nat-order-design.md §1). It landed as a definition — Lt(n, m) := Le(Succ(n), m) — not as a second recursion, so the one-relation-or-two question is untouched at the class level and this issue keeps it. Two data for it. (a) At Nat the derived presentation is free in a way that argues for one relation plus a definition: lt_succ_iff_le and lt_succ_self are both definitional, and the strict kit is nine short lemmas that are all Le's kit read at Succ(n). (b) Cmp did NOT grow a lt field this round — it carries le, le_refl and le_dec — so whichever way this issue goes, no consumer has been committed.
- 2026-08-20: The stdlib review asked whether reflexive/transitive behavior
  should itself be expressed by operator-indexed typeclasses. Keep the useful
  evidence here: for orders, those laws belong together in `Preorder` and its
  hierarchy rather than as globally resolved microclasses for `Refl<r>` and
  `Trans<r>`. Generic relation-property records may still be useful as theorem
  parameters, but making every law independently canonical would multiply
  resolution choices and lose the algebraic bundle a consumer normally wants.
- 2026-11-02: **Decided and closed** (docs/strict-order-presentation-design.md). Option B holds where `<` is primitive. `StrictOrder(≈, <, ≤)` takes both relations as indices, and its agreement is Bishop's `x ≤ y ↔ ¬(y < x)`. That, with tightness, makes it the family of constructive *linear* orders. `Preorder`/`PartialOrder` keep one relation. This reverses the 2026-08-16 target `Preorder<A>(le, lt)`, because each of that entry's three reasons (Nat's computing `Lt`, products and ordinals, well-founded `<`) is served by the strict-first family. B's agreement `lt ↔ le ∧ ¬ge` would force a product's `<` to be the strict part anyway. New in this round: the classes present their relational views as tagged parents. `StrictOrder` has `Transitive(<)` and the four `≈` pairs, and `PseudoOrder` has `Preorder(≤)` and the two `<`/`≤` pairs. So a generic `calc` steps through `<`, `≈` and `≤`, which was refused before. Carriers fill the views by reference. The notation requirement, that `(≈, <, ≤)` is one package, moves to [[class-default-operators]]. Retiring the per-carrier copies of the views waits on [[class-inherited-field-implementations]]. The import cost it exposed is [[class-parent-names-resolve-in-client-scope]].
