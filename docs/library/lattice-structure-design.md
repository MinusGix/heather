# Lattices: meets and joins over an order modulo `≈`

Issue: `issues/lattice-structure-api.md`. Module: `lib/std/algebra/lattice.hthr`
(the classes and the `Nat`/`Int` instances), `lib/std/num/float/dyadic.hthr` (the
`Dyadic` instance). Probes: `lib/_tests/std/algebra/lattice_tests.hthr`. Builds on
`order.hthr` (`Preorder`, `PartialOrder`, `ProductOrder`) and `algebra_rel.hthr`
(`Mergeable`).

## 1. What the issue asked

Meet and join semilattices, lattices and bounded lattices, with the connection
between their algebraic laws and the order's universal properties. The relation
and the operations are explicit indices, so one carrier can carry several orders
and operations. Start from the `Nat` and `Int` `min`/`max` laws, add a product
control, and decide whether order-derived and algebraically presented lattices
are separate interfaces joined by constructors or one canonical theory.

## 2. Decisions

**One canonical theory, presented by the order.** `MeetSemilattice(≈, ≤, ⊓)`
has three fields, the greatest-lower-bound property: `meet_le_l`, `meet_le_r`
and `le_meet`. Commutativity, associativity, idempotence, monotonicity,
respect for `≈` and absorption are theorems. The algebraic presentation is not
a second interface with its own theorem library. It is `algebra_rel`'s existing
`Mergeable(≈, ⊓)`, a commutative idempotent semigroup modulo `≈`, and the two
meet by constructors:

- `MeetSemilattice::mergeable()` reads the algebra off the order.
- `Mergeable::meet_semilattice()` builds the order `MergeLe(≈, ⊓)`, which is
  `x ⊓ y ≈ x`, from the algebra. Its meet is the operation itself.
- `MeetSemilattice::le_iff_meet` says the round trip gives the order back:
  `x ≤ y ↔ x ⊓ y ≈ x`.

The order side is the canonical one because every carrier here arrives with its
order first (`Nat::Le`, `Int::Le`, `Dyadic::Le`), and the universal property is
what the instances can prove directly from their `min`/`max` lemmas. A carrier
that arrives with an operation (`Bool`'s `&&` in the probes) gets its order from
the constructor without writing one.

**`≈` is an index of its own.** The classes extend a new
`PartialOrderRel(≈, ≤)`: a preorder whose antisymmetry lands in `≈`. This is
the shape the rest of the algebra already has (`StrictOrder(≈, <, ≤)`,
`Semiring(≈, +, *)`), and the relation-indexed decision of
`issues/relation-indexed-algebra.md`. `order`'s `PartialOrder(R)` is the case at
identity, and `PartialOrder::rel` turns one into the other. `Nat` and `Int` are
lattices at `RelId`, so with `semiring`'s `designation ≈ at Nat/Int := RelId`
their laws read as equations. `Dyadic`'s `min`/`max` form a lattice modulo
`Dyadic::Same`, where two spellings of one number are `≈` and not `=`. The
identity-only reading could not have held that instance.

The preorder and the two mixed chains (`Trans(≈, ≤, ≤)`, `Trans(≤, ≈, ≤)`) are
tagged parents (`le_preorder`, `same_le`, `le_same`), as `StrictOrder`'s are
(`docs/library/strict-order-presentation-design.md`). A carrier with those instances
registered fills them by reference, so the `Nat`, `Int` and `Dyadic` instances
write only `le_antisymm`. Everything else (`le_refl`, `le_trans`, `le_of_same`,
`le_respects`) is a theorem at `PartialOrderRel`.

**Join is written as the meet's dual, not derived from it.** `JoinSemilattice`
has the least-upper-bound fields, and its theorems are the meet's read upside
down. Proving them once would mean spending a generic theorem at a dictionary
built in place (`MeetSemilattice` at `Converse(≤)`), and resolution only finds
registered instances. The proofs are short, so they are written out and the
duality stays a pattern. If a generic theorem can later take a constructed
dictionary, the join half becomes one constructor and a set of one-line calls.

**Bounds are capabilities of their own.** `OrderBot(≤)` and `OrderTop(≤)` each
carry one element and one law. `Nat` has a bottom and no top, and `Int` has
neither, so `BoundedLattice` (a lattice with both) has no instance among the
number carriers. The bound laws (`OrderBot::bot_meet`, `bot_join`,
`OrderTop::top_meet`, `top_join`) are stated at the weakest pair, for example
`MeetSemilattice + OrderBot`. The merged constraint reaches `Nat` without
`Nat` registering anything beyond its `Lattice` and `OrderBot`.

**The lattice operations have notation.** `⊓` is a new token, beside the
existing `⊔`. It sits on the multiplicative rung, as `∙` does, so `x ⊔ y ⊓ z`
reads as `+` over `*`. Like `⊔` it has no fallback name, so it means only what a
binder spelled with it means (`meet as ⊓`). It needed a token because a section
binds an index implicitly only through a symbol. Without one, every lattice
theorem would take its meet as an explicit argument.

## 3. What each carrier fills

| Carrier | Layer | Notes |
| --- | --- | --- |
| `Nat` | `Lattice` at `RelId`, `OrderBot` | `min`/`max`; bottom `0` |
| `Int` | `Lattice` at `RelId` | `min`/`max`; no bounds |
| `Dyadic` | `Lattice` modulo `Dyadic::Same` | `min`/`max` by the order's decision; new `le_min_of`, `max_le_of` |
| `Pair<A, B>` | `product_lattice`, `product_partial_order_rel` | `ProductOrder` as both relation and order, `ProductOp` componentwise |
| `Bool` (probe) | `Mergeable::meet_semilattice` at `&&` | the order built from the algebra |
| `Nat` at `≥` (probe) | `Lattice(RelId, Ge, max, min)` | a second lattice on one carrier; the roles of the operations swap |

`Int`'s identity setoid (`Equivalence<Int>(RelId<Int>)`) moved from `semiring`
to `order`, beside `Nat`'s in `relation_props`. Registering `PartialOrderRel<Int>`
in a module that does not import `semiring` otherwise mints a second copy of
that parent, and any later module importing both refuses the world
(`stored module metadata conflicts with the accepted instance registry`).
`semiring` now imports `order`.

## 4. Not done here

- **Distributive, modular and complemented lattices, and Heyting algebras.**
  `Nat`, `Int` and `Dyadic` are distributive, but no consumer asks for the law
  yet. It is one class over `Lattice` with one field.
- **A lattice from any decidable linear order.** Each carrier writes its own
  `min`/`max` today. A generic `if`-based constructor would read them as one
  definition and needs coincidence lemmas at the carriers.
- **`Rat` and `CReal` lattices.** Neither has a `min`/`max` pair under those
  names, so neither has an instance. `CReal`'s would be the constructive one,
  where `min` is computed from approximations and needs no decision.
- **Suprema and infima over families.** Complete lattices, and the order
  completeness of the reals, belong to `math-reals`.
- **Index inference through a definition.** A hypothesis whose type is a
  carrier's definition (`Rat::Same(x, y)`) does not pin a generic theorem's
  indices even when it unfolds to the theorem's statement. `Rat::same_trans`
  restates its hypotheses at `Int` before calling
  `OrderedSemiring::cross_same_trans` (`issues/index-inference-through-unfolding.md`).
