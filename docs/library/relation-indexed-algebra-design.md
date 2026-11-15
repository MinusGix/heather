# Relation-indexed algebra: one theory, identity as a specialization

Owner: [relation-indexed algebra](../../issues/relation-indexed-algebra.md).
Related: [operation-indexed classes](../language/classes/operation-indexed-classes-design.md) §8
and §14.5, [lattices](lattice-structure-design.md), the semiring layers
(`lib/std/algebra/semiring.hthr`).

## 1. The problem

Two one-operation hierarchies had grown side by side:

- `algebra`'s identity classes, `Semigroup`/`Monoid`/`CommMonoid`/`Group`
  over `op`, laws stated with `=`, with `mconcat`, `mconcat_single`,
  `op_unit_of_comm` and `op_inv_unique`;
- `algebra_rel`'s relational classes, `SemigroupRel`/`MonoidRel`/
  `CommMonoidRel`/`GroupRel` over `(≈, op)`, with `MonoidRel::fold`,
  `fold_append`, `GroupRel::inv_unique` and the commutative fold lemmas
  (these lived in `semiring`).

They were maintained independently. `Nat` and `Int` registered *both*: an
identity `CommMonoid<Nat>(add)` in `algebra` and a `CommMonoidRel<Nat>(RelId,
add)` in `semiring`, the same four laws filled twice; `op_inv_unique` and
`GroupRel::inv_unique` were two proofs of one fact; `mconcat` and
`MonoidRel::fold` were two folds. A theorem proved for one was unavailable to
a client of the other. That is the "two independently maintained theorem
libraries" the issue rules out.

## 2. The decision: a generalized source theory

The relational classes are the source theory. Each identity class is its
relational counterpart **at `RelId`**, declared as a child at that computed
index and with no fields of its own:

```heather
class Semigroup<A>(op as ∙: A → A → A) extends SemigroupRel<A>(RelId<A>, op) {}
class Monoid<A>(op as ∙: A → A → A) extends Semigroup<A>(op), MonoidRel<A>(RelId<A>, op) {}
class CommMonoid<A>(op as ∙: A → A → A) extends Monoid<A>(op), CommMonoidRel<A>(RelId<A>, op) {}
class Group<A>(op as ∙: A → A → A) extends Monoid<A>(op), GroupRel<A>(RelId<A>, op) {}
```

The alternative, generated companion interfaces (a generator emitting an
identity class and a copy of each theorem from the relational source), was
rejected: it still produces two libraries, only mechanically, and every
generated theorem is a second declaration to check, name and keep in sync
with its source. The specialization needs no generator. What it needed was
one language rule (§3).

What a user sees:

- **Identity statements are unchanged.** `RelId<A>(x, y)` is `x = y` by
  unfolding, so `A.assoc(x, y, z)` at a `Monoid(op)` binder is an equation,
  and `mconcat_single`, `op_unit_of_comm` and `op_inv_unique` keep their
  signatures.
- **Every relational theorem is an identity theorem.** A `Monoid(op)` binder
  upcasts to `MonoidRel(RelId, op)` by the ordinary ancestor path, so
  `MonoidRel::fold_append` applies at `Monoid<Nat>(add)` as it does at
  `MonoidRel<Rat>(Rat::Same, add)`. The identity theorems are one-line
  specializations of the relational ones: `op_inv_unique` is
  `GroupRel::inv_unique` at identity, `op_unit_of_comm` is
  `CommMonoidRel::unit_r_of_comm`, and `mconcat` is `MonoidRel::fold` by
  definition.
- **One registration per structure.** `instance CommMonoid<Nat>(Nat::add)`
  registers `CommMonoidRel<Nat>(RelId<Nat>, Nat::add)` and its ancestors as
  its parents, so `semiring`'s `CommSemiring<Nat>(RelId, add, mul)` finds
  them by reference; the duplicate relational instances at `Nat` and `Int`
  are gone.

## 3. The language rule: a parent at a computed index

Layer 1 restricted an `extends` index argument to one of the child's own
value parameters, so instantiating a parent was a rename
(operation-indexed-classes-design §14.5). The restriction is relaxed: an
index argument may be any expression over the child's parameters
(`RelId<A>`). The parent's index name and body symbol then read as that
expression, and its field types are instantiated by substitution.

The mechanism is one walk. `traits::Ren` carries, beside the rename, images
for value names (an index expression) and for type names (a composite
carrier). Three places instantiate an ancestor written in a class's names,
and all three now go through `Ren::at_use`:

- declaring a child (`parent_view`: the parent's fields and its own
  ancestors, in the child's names);
- declaring an instance (`ancestor_index_at`: `RelId<A>` under
  `Monoid<A>(op)` becomes `RelId<Nat>` at `instance Monoid<Nat>(add)`, which
  is the registry key the parent is looked up and registered under);
- filling an index slot from a binder in scope (`scope_index` and the
  index-from-scope proposal in `dispatch/dictionary.rs`: a `Monoid<A>(op)`
  binder proposes `(RelId<A>, op)` for a `MonoidRel` goal).

Two fibers are the same when their index arguments are the same parameter or
the same computed expression spelled alike (`same_index_arg`): syntactic, as
the registry key is. That is what lets `CommMonoid` reach `MonoidRel(RelId<A>,
op)` through both `Monoid` and `CommMonoidRel` and keep one copy.

**Clients need no new imports.** A client of `algebra` that never imports
`algebra_rel` or `relation` still forms these dictionaries and reads their
members, which needed three rules
(issues/class-parent-names-resolve-in-client-scope.md):

- a class records each parent by its declaration key, and every global a
  computed index names too (`relation::RelId<A>`), so instantiating an
  ancestor in the client's scope resolves (`traits::qualified_parent`);
- a member's owner is a dot-sugar candidate when the client can name it *or*
  a class the client can name reaches it as an ancestor
  (`declaring_classes`), and its goal is built by key: `G.unit` under
  `G: CommMonoid(o)` reaches `MonoidRel`'s `unit`; the scope upcast keys the
  goal's class and the binder's by their tags' declarations, not by name;
- a registered instance's generated global (`algebra::Nat::CommMonoidRel#…`)
  resolves by its key wherever the instance is visible, so a child instance
  fills an inherited field by reference from a parent registered in a module
  it never imported (`semiring`'s `CommSemiring<Nat>` from `algebra`'s
  monoids) — in a real run the common prelude happened to reach `algebra`,
  but a run without it did not;
- the value-slot refusal names the nearest class the client can name
  (`Semigroup<Bool>(Bool::and)` for `assoc`, not `Associative<Bool>(RelId,
  Bool::and)`), since that is the dictionary the reader can write.

Not changed: the upcast itself already projected the child's fields and
checked the built parent against the goal, so it needed nothing. The
linked-constraint join (`resolve.rs`, `A: X + Y`) still reads parents by
name, so a merged constraint whose parent sits at a computed index does not
join; no client asks for one yet.

## 4. Relation plumbing

- **Generic theorems** state laws with `≈`, the parent's body symbol, which a
  binder's `same as ≈` spells. A constraint links the relation by its slot
  (`MonoidRel(same, op)`) when the statement names it, and leaves it to scope
  when only the dictionary does (`MonoidRel(≈, op)`).
- **Identity carriers** read those statements as `=`: at `Nat` and `Int` the
  designation `≈ at Nat := RelId` (semiring) supplies the relation when
  nothing in scope pins it; at an identity binder the scope binder proposes
  `RelId<A>` itself.
- **Specializing a relational theorem by hand** passes the relation when the
  theorem links it: `MonoidRel::fold_single(RelId<A>, op, x)`.
- **The carrier alone never chooses.** `Bool` and `List<A>` have no `≈`
  designation: a relational theorem there is reached through an identity
  binder or an explicit `RelId`, never by guessing that a carrier's structure
  relation is identity. `List<A>` in particular also carries the membership
  setoid (`list_setoid`'s `Mergeable`), so identity is not even the only
  candidate.

The `=`-as-structure-relation experiment (writing `=` in a generic section
for the bound relation, with a separate spelling for identity) was not run:
the specialization makes it unnecessary for the identity carriers, whose
statements already read as `=`, and at a relational carrier `≈` is the honest
spelling. It stays an open experiment, not a change to `=`.

## 5. Migration cost, measured against the existing library

| What | Before | After |
|---|---|---|
| Identity class declarations | 4 classes, 7 law fields | 4 empty children |
| Identity dictionary at `Monoid<A>(op)` | 4 fields (`assoc`, `unit`, `unit_l`, `unit_r`) | 8: the setoid's 3 and `respects2` join them |
| Instance bodies at `Nat`, `Bool` (×2 each), `Int` (×2) | the laws | unchanged: setoid and `respects2` fill by reference |
| `Group<Int>(add)` | `inv`, `inv_l`, `inv_r` | `+ inv_respects := cong` |
| `instance<A> Monoid<List<A>>(append)` | 4 fields | `+ 4` inline setoid/congruence fields (a generic parent offers no fill by reference) |
| New registrations | — | `Equivalence<Bool>(RelId)`, four `Respects2` at `Nat`/`Bool` (moved from `semiring` at `Nat`); `Equivalence<Int>(RelId)` and `Int`'s two `Respects2` moved into `int` |
| Duplicate relational instances | `Nat` ×2, `Int` ×3 in `semiring` | deleted |
| Theorem statements | — | unchanged (`mconcat_single`, `op_unit_of_comm`, `op_inv_unique`, `Int::neg_unique`) |
| Duplicate proofs | `op_inv_unique` (9 lines) beside `GroupRel::inv_unique` | one proof; the identity name is a call |
| One-operation relational consumers | in `semiring` | in `algebra_rel`, next to their classes; names unchanged |

The dictionary growth is the one real cost: an identity monoid carries a
setoid and a congruence proof that are trivially `refl`/`sym`/`trans`/`cong`.
They are proof-only fields, shared by reference, so no instance author writes
them at a concrete carrier.

A structure's field **display** changes too: a law's type now spells
`RelId(…)` where it spelled `=` when a diagnostic prints a field's declared
type. Goals at concrete carriers are unaffected, since they are elaborated
from the statement, not the field.

## 6. Dictionary coherence

The finite-set stress test (issue §"Dictionary coherence") is untouched by
this round and stays the policy: units are unique modulo the relation; the
selected parent dictionary is kept exactly through inheritance; independently
built dictionaries are never merged. The specialization respects it by
construction: the identity instance *is* the relational instance's child, so
there is one dictionary, not two that correspond.

## 7. What is left

- **Ordered and two-operation layers already were relational** (semiring,
  ordered field, lattice); nothing to migrate there.
- `class-inherited-field-implementations` would let `Group<Int>` and the
  rings omit the derived `zero_mul`/`inv_respects`-style fields.
- The linked-constraint join at a computed parent index (§3), when a client
  asks for it.
