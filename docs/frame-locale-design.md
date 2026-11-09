# Frames and locales: a predicative foundation

Issue: `issues/frame-and-locale-foundations.md`. Modules: `lib/std/locale/frame.hthr`
(the classes, homomorphisms, locale maps, `Omega`, points, spatial frames),
`lib/std/locale/nucleus.hthr` (nuclei and sublocales),
`lib/std/locale/formal_topology.hthr` (presentations). Probes:
`lib/_tests/std/locale/frame_tests.hthr`. Builds on nothing but `logic`;
`lattice.hthr`'s finitary classes are not reused, for the reason in §2.

## 1. What the issue asked

Complete lattices, frames (finite meets distributing over arbitrary joins),
frame homomorphisms, locales as the opposite category, and a presentation
basis that works in a predicative system. Confront universe size and the
representation of arbitrary joins directly; points only as a derived notion.

## 2. Universe policy

**Joins are of small families, never of subsets.** `sup: (I: Type) → (I → A) → A`.
A subset-indexed join (`arend-lib`'s `Join : (E → \Prop) → E`) is small only
under an impredicative `Prop`, which Heather does not have. A family indexed
by a small type is the predicative replacement and loses nothing: a "subset"
`U: A → Type` of a small carrier is the family `λ (e: Exists<A>(U)) => e.witness`.

**The frames that exist are large.** The frame of truth values holds a small
type in each element, the frame of opens of `X` holds a predicate `X → Type`,
and a presented frame holds families of basic opens. Each carrier quantifies
over `Type`, so it lives at `Type<1>`. A nontrivial frame with all small joins
and a carrier at `Type<0>` would need propositional resizing (de Jong and
Escardó's result for small complete lattices), so this is not a defect of the
encoding. The order stays small, `A → A → Type` ("locally small"), and the
indexing types stay small. The negative control in the probes is a frame at
`Bool`, refused because the universes do not cumulate.

**So the classes are declared at `Type<1>`**, and that is why they do not
extend `lattice.hthr`'s `MeetSemilattice`/`PartialOrderRel`: those are classes
over `Type<0>` carriers, and a class is not level-polymorphic
(`issues/implicit-level-polymorphism.md`). `Preorder1` is `order`'s `Preorder`
at `Type<1>`, a copy that level polymorphism would retire. The copies are
kept to what frames need.

**Equality is the preorder's.** Two opens are the same when each is below the
other, and there is no antisymmetry field. A frame of predicates then needs no
function extensionality, the same choice `lattice.hthr` made by taking `≈` as
an index, taken one step further because a frame's `≈` is always the mutual
order. Every law is a field only in its nontrivial direction
(`meet_sup_le`, a homomorphism's `map_meet`, `map_top`, `map_sup`); the other
direction is a theorem (`Frame::meet_sup`, `FrameHom::meet_law`,
`FrameHom::sup_law`).

**Σ, not truncation.** Joins in `Omega` and `Opens` are `Exists` (a Σ). The
truncated `∥Σ∥` would make the opens propositional, but nothing here needs it,
since every comparison is by the order and never by equality of opens.

## 3. Classes, and what had to change in the elaborator

```
Preorder1<A: Type<1>>(≤)
FiniteMeets<A: Type<1>>(≤, ⊓)       extends Preorder1   — meets, top
SupLattice<A: Type<1>>(≤, sup)      extends Preorder1   — small joins
Frame<A: Type<1>>(≤, ⊓, sup)        extends both        — meet_sup_le
```

**Layered by what statements mention.** A client at a concrete carrier
(`Opens<Nat>`) pins a generic theorem's indices from its own statement: `≤`
and `⊓` through the carrier's designations, the join by name. A theorem
stated in a section whose class has an index the statement does not mention
cannot be called from such a client, because nothing pins that index. So
meet-only theorems live at `FiniteMeets`, join-only ones at `SupLattice`, and
only distributivity at `Frame`. For the same reason the bottom and the binary
join (`SupLattice::bot(sup)`, `SupLattice::join(sup, x, y)`, joins over `False`
and `Bool`) are functions of the join operation, not of the section: the
section form refuses a declaration whose head does not determine `sup`. The
join has no symbol, so it cannot be bound in a section the way `⊓` is; it is
an implicit section parameter instead (`({sup: …})`).

**A class carrier declared at a universe.** `class C<A: Type<1>>` was already
accepted: like a class over a type constructor (`Bind<M: Type → Type>`), its
carrier is the record's leading *value* parameter. Instances registered and
resolved, but three readings did not know about the leading value:

1. `A.member` in a section over such a class (the type projection, and
   receiver dispatch) built its goal with `A` as a type argument the record
   does not have, so every `A.le_trans(…)` was refused as `no instance for ``.
   `index_vargs` now returns the goal's type arguments too, and at a carrier
   declared at a universe passes the carrier's code as the leading value
   argument instead (`universe_carrier`, `valparam_args_after`).
2. `Omega::Frame(…)`, the `T::C(index)` spelling of an instance, had the same
   mismatch, fixed by the same helper.
3. The record's remaining value-parameter types (`le: A → A → Type`) were read
   with `A` bound only as an alias, and type parameters are looked up before
   aliases, so a caller's own type parameter named `A` captured it
   (`FrameHom::comp`, whose first type parameter is `A`, saw the class's `A`
   as its own). A leading value at a universe is now also bound as a type
   parameter, which shadows correctly.

A record still cannot declare `<A: Type<1>>`
(`issues/record-universe-parameters.md`), so `FrameHom`, `LocaleMap` and
`Nucleus` take their carriers as value parameters (`FrameHom(A, B, map, …)`).

## 4. Homomorphisms, locales and points

`FrameHom(A, B, map, ≤ₐ, ⊓ₐ, ⊤ₐ, supₐ, ≤ᵦ, ⊓ᵦ, ⊤ᵦ, supᵦ)` is a record in the
shape of `morphism.hthr`'s `OrderedRingHom`: the operations are parameters, so
a law is stated at the carriers' own operations. Identity and composition are
`FrameHom::id` and `FrameHom::comp`.

A locale is its frame; only the direction of maps changes.
`LocaleMap(X, Y, …)` holds `inv: Y → X` and a `FrameHom` from `Y`'s opens to
`X`'s. There is no separate locale type, because a locale has no data beyond
its frame.

**Points are derived.** `Omega` is the frame of opens of the one-point locale
(small propositions, `≤` implication, `⊓` conjunction, `sup` Σ), and
`Point(…) := LocaleMap(Omega, X, …)`. The completely-prime-filter reading is
proved rather than assumed: `Point::in_top`, `in_mono`, `in_meet`, `in_sup`
(a point lies in a join only through one of its terms). Nothing defines a
locale by its points.

**Spatial frames.** `Opens<X>` (predicates on a small type, ordered by
inclusion) is a frame; each `x: X` is a point (`Opens::point`) and each
function is a map of locales by preimage (`Opens::map`).

## 5. Nuclei: quotients without quotient types

A nucleus `c` on a frame (monotone, inflationary, idempotent, preserving
binary meets) presents a sublocale, and every quotient frame arises this way.
Its fixed points form a frame, which here needs no subtype: `Nucleus::frame`
keeps the carrier, the meets and the joins and changes only the order, to
`x ≤ c(y)`. Each open is then the same as its closure
(`Nucleus::closure_same`), so the preorder *is* the fixed-point frame up to
its equivalence. The inclusion of the sublocale is the identity on opens
(`Nucleus::inclusion`), a frame homomorphism into the finer order exactly
because of the nucleus laws. The first instance is double negation on
`Omega` (`Omega::dn_nucleus`), whose sublocale is the Boolean one.

Relation-indexed classes are what make this cheap: the sublocale's frame is a
second `Frame` on the same carrier at a different order index, not a new type.

## 6. Presentations: formal topologies

A formal topology is a small basis `P`, a preorder on it, and a cover
`a ◁ U` with four rules: reflexivity, transitivity, the `≤`-left rule, and
localisation (`a ◁ U` and `a ◁ V` give `a ◁ U ↓ V`, the families' formal
meet, `Opens::down_meet`). `FormalTopology::frame` builds its frame on
`Opens<P>`: `U ≤ V` when every member of `U` is covered by `V`, meets are
`↓`, joins are unions. Joins need no rule at all, because a union of a small
family of families is a family; this is the predicative content of the
presentation. `FormalTopology::sup_basic` says the basic opens `↓a` form a
basis: every open is the join of those it contains, indexed by the small type
of its members.

The cover is **axiomatic**: any relation with the four rules presents a frame.
The first instance is the Alexandrov topology of a preorder (no covering
axioms, `a ◁ U` when `a` lies below a member), whose frame is the down-sets.

This is the route `arend-lib` takes through preorder sites and `SiteLocale`
(`docs/arend-survey.md` §7), in its formal-topology form (Sambin; Coquand,
Sambin, Smith and Valentini, "Inductively generated formal topologies").

## 7. Not done here

- **Covers generated by axioms.** A particular locale (the reals, a spectrum)
  is presented by a small *axiom set* `C(a)` of covers of each basic open,
  and its cover is the least relation closed under the rules, an inductive
  family with an infinitary premise. Proving it satisfies localisation needs
  the axioms localised and a double induction. Filed as
  `issues/inductive-formal-covers.md`; `localic-real-numbers` now waits on it.
- **Heyting implication.** Every frame is a Heyting algebra, but
  `x ⇒ y := sup{z | z ⊓ x ≤ y}` is a join indexed by elements of a large
  carrier, so it is not formable in general. In a presented frame it is,
  over the small basis. Logged on `inductive-formal-covers`, where the basis
  is.
- **Products, coproducts and the localic product.** Coproducts of frames are
  easy (pointwise); the product of locales is a presented frame and comes with
  the inductive covers.
- **Generic theorems at a constructed dictionary.** A presented frame is a
  `Frame` value built by a function, not a registered instance, so the generic
  `Frame::…` theorems cannot be called at it; its fields can. This is the
  limitation `docs/lattice-structure-design.md` §2 notes for duality.
- **Level polymorphism**, which would merge `Preorder1` with `Preorder` and let
  the frame classes extend `lattice.hthr`'s
  (`issues/implicit-level-polymorphism.md`).
