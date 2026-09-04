# Your own thing with laws: mergeable summaries

Status: illustrative design, 2026-09-04. This document mixes existing Heather
class/record ideas with proposed relational notation and proof generation.
The snippets have not been checked and are not a syntax commitment.

The [three small experiences](../three-small-transfer-experiences.md) use
interfaces someone else defined. Here we write one ourselves.

Suppose your program collects summaries from several sources. A summary might
be the highest score seen, a collection of discovered names, or a set of enabled
features. You want to combine summaries without caring about delivery order
or repeated deliveries.

The idea you want to express is:

> These values can be merged. Merging respects what counts as the same value.
> Grouping, order, and repeated copies do not change the resulting meaning.

## 1. Describe the agreement

There are three things to name:

- The kind of value, `A`.
- When two values mean the same thing, `same`.
- The operation that combines them, `merge`.

```heather
class Mergeable<A>(
    same as ≈: A → A → Type,
    merge as ⊔: A → A → A)
    extends Equivalence<A>(same),
            Respects2<A>(same, same, same, merge),
            Associative<A>(same, merge),
            Commutative<A>(same, merge),
            Idempotent<A>(same, merge)
{}
```

These proposed law classes let the author name common properties directly.
`Mergeable` combines them and adds no fields of its own. `Respects2` here is
an evidence-bearing interface for the shared respectful predicate; it must
not introduce a second definition of compatibility. The repeated A is elided
in the name for this homogeneous example, not a restriction on the underlying
heterogeneous relational calculus.

The relation is an index of the algebraic laws as well as the operation:
commutativity modulo `same` can hold when commutativity by identity does not.
An identity-specialized shorthand can omit that index when it is unambiguous.

To understand what is being combined, expand the named laws into their fields:

```heather
// Conceptual expansion of the parents, not a second Mergeable declaration.
compatible: (x, x2, y, y2: A) →
    x ≈ x2 → y ≈ y2 → (x ⊔ y) ≈ (x2 ⊔ y2)
assoc: (x, y, z: A) → (x ⊔ y) ⊔ z ≈ x ⊔ (y ⊔ z)
comm:  (x, y: A) → x ⊔ y ≈ y ⊔ x
idem:  (x: A) → x ⊔ x ≈ x
```

Read the fields as sentences:

| Field | Meaning |
| --- | --- |
| inherited `Equivalence` | “Same” is reflexive, symmetric, and transitive |
| `compatible` | Replacing inputs by equivalent ones preserves the merge result |
| `assoc` | Grouping merges differently gives the same result |
| `comm` | Swapping the inputs gives the same result |
| `idem` | Merging a value with itself adds nothing |

The long `compatible` field is shown only to explain the named interface.
Users can refer to the shared law without repeatedly spelling its quantifiers.

`≈` and `⊔` are short local names for the explicitly supplied relation and
operation. They do not redefine identity `=` or select an operation for all
values of A. The `as` spelling follows Heather's operation-binder direction;
support for this complete relational spelling remains proposed.

Why put `same` and `merge` in the header? They identify the agreement. The same
carrier might support several different meanings and merge operations. The
fields contain the evidence that this particular pair satisfies the agreement.

No field says that all summaries have an empty value, support subtraction, or
can be compared by a decision procedure. Those are separate capabilities to
add if a client needs them.

## 2. Supply an implementation

For natural-number high scores, “same” can be ordinary identity and merge can
be maximum:

```heather
instance Mergeable<Nat>(RelId<Nat>, max) {
    compatible := derive(),
    assoc := max_assoc,
    comm := max_comm,
    idem := max_self,
}
```

`max` and the lemma names here stand for a supplied implementation and its
proved facts; this sketch does not claim those exact declarations exist today.
The identity equivalence is inherited from the selected existing dictionary.

`derive()` means “attempt to construct the proof required at this field.”
Compatibility with identity follows from ordinary equality congruence.
The other fields refer to mathematical facts about maximum. They could also
be proved inline or requested from an appropriate generator.

An instance is evidence, not an assertion that Heather takes on trust. Every
supplied or generated field must check before the instance is available.
Heather cannot infer associativity, commutativity, or idempotence merely from
the type `Nat → Nat → Nat`.

Now use a different implementation: lists representing collections where
order and repetitions do not matter.

```heather
instance<A> Mergeable<List<A>>(SameMembers<A>, append) {
    // The selected SameMembers equivalence supplies the inherited laws.
    compatible := append_same_members,
    assoc := append_assoc_same_members,
    comm := append_comm_same_members,
    idem := append_self_same_members,
}
```

For this small example, `SameMembers` uses identity equality of elements and
mutual membership of the lists. Its equivalence and the four named lemmas must
be proved first; they are inputs to this instance, not generated assumptions.
No element equality decider is needed merely to concatenate lists or state
and prove these membership laws.

Appending `[1]` to `[2]` and appending `[2]` to `[1]` produce different lists,
but the lists contain the same members. Similarly, `[1] ++ [1]` and `[1]`
are different lists with the same members. The relation is what makes this a
valid implementation of the requested agreement.

Both instances implement the same *kind of interface*. This does not assert
that a Nat score and a list of names represent the same object, or that the
two implementations have a correspondence between their carriers.

## 3. Prove a useful fact once

A repeated delivery should not change the accumulated summary:

```heather
theorem merge_twice<A: Mergeable(same, merge)>(
    same as ≈: A → A → Type,
    merge as ⊔: A → A → A,
    state, incoming: A):
    (state ⊔ incoming) ⊔ incoming ≈ state ⊔ incoming
{
    calc {
        (state ⊔ incoming) ⊔ incoming
            ≈ state ⊔ (incoming ⊔ incoming)
                := A.assoc(state, incoming, incoming),
            ≈ state ⊔ incoming
                := A.idem(incoming),
    }
}
```

The last step uses `idem` inside the surrounding merge. Heather's proposed
relational calculation support composes the `compatible` proof automatically.
There is no handwritten “merging on the left preserves equivalence” helper.

The carrier constraint supplies the dictionary and its projections through A.
The relation and operation are still explicit binders in this version. In everyday use, the relation, operation, and dictionary
can be inferred when the surrounding interface pins them down. An ambiguous
choice remains an error; theorem search must not choose a meaning for the user.

This theorem works for both examples:

```text
max(max(current_score, reported_score), reported_score)
    = max(current_score, reported_score)

(known_names ++ incoming_names) ++ incoming_names
    ≈ known_names ++ incoming_names
```

The first specializes the relation to identity, so its conclusion is ordinary
equality. The second is equality of represented collections. No new proof of
the generic calculation is required.

Notice that this particular theorem only used compatibility, associativity,
and idempotence. If a later client needs exactly those weaker assumptions,
request just the named law classes it uses. The common vocabulary lets a client
state weaker requirements without inventing another monolithic interface.

## 4. Write a client that consumes the agreement

```heather
fn receive<A: Mergeable(same, merge)>(
    same: A → A → Type,
    merge: A → A → A,
    current, incoming: A) → A
{
    merge(current, incoming)
}
```

The body is ordinary code. A relational derivation for this client can produce:

```text
same(current,current2) → same(incoming,incoming2) →
same(receive(current,incoming), receive(current2,incoming2))
```

The fixed relation, merge operation, and dictionary are omitted from the
displayed calls for readability. This result is built from `A.compatible`.
It is a separate checked certificate, not a consequence of raw function typing.

`merge_twice` explains why retrying a delivery preserves the summary's meaning.
The compatibility certificate explains why changing its representation
preserves that meaning. These are different guarantees, supplied by different
parts of the same interface.

The example makes no claim about a distributed delivery protocol, synchronization,
or effects. It proves a fact about repeated pure merge operations. A runtime
that sends notifications on every call would need a separate effects theorem
before suppressing those calls.

## 5. What happens when a law is unfinished?

Suppose you have a custom merge implementation and write:

```heather
instance Mergeable<MySummary>(same_summary, combine) {
    compatible := combine_compatible,
    assoc := combine_assoc,
    comm := combine_comm,
    idem := ?,
}
```

Assume the inherited equivalence has already been provided. `?` is a proposed
use of Heather's reporting-hole convention at this class-law field. It asks
to see the obligation; it does not put an unproved instance into scope.

The normal message is sufficient:

```text
The idempotence law for this instance is unfinished.

Required:
    (x: MySummary) → same_summary(combine(x,x), x)

This is the remaining field needed to complete this Mergeable instance.
Once proved, the instance supports the merge_twice theorem.
```

For a failed automatic compatibility attempt:

```text
combine has not been shown to preserve same_summary.

Required:
    same_summary(x,x2) → same_summary(y,y2) →
    same_summary(combine(x,y), combine(x2,y2))
```

Neither message says the function is invalid. The proof may need a lemma that
the generator does not know, or the generator may have exhausted its budget.
The detailed result should identify that actual status.

An optional bounded counterexample search can improve the message. For example,
an attempted additive Nat instance would fail its idempotence requirement at
`x = 1`, since `1 + 1 ≠ 1`. Report this only after validating the witness. A
search that finds nothing reports its bound and lack of a witness, not a proof.

The law's type is already known from the class field. Displaying it and letting
the author supply a proof requires no smart counterexample finder.

## 6. The agreement creates specific opportunities

A consumer or optimizer might propose:

```text
Candidate: remove a repeated merge of the same incoming summary
Required: the merge_twice guarantee in the consumer's observation relation
Would enable: one fewer merge operation
```

For high scores, the replacement preserves the actual Nat result. For the list
implementation, it preserves members but can change list length and storage.
The replacement is valid for a client observing the collection through this
interface. It is not justified for an unrelated raw-list client that observes
length. The opportunity must state which observations it preserves.

Likewise, one fewer merge is a structural claim. A claimed speedup needs cost
evidence, and removing calls with effects needs an effects-aware argument.

## 7. What the author supplies, and what Heather can do

| The author supplies | Heather can help with |
| --- | --- |
| The relation that expresses sameness | Reusing its equivalence laws |
| The operations and desired mathematical laws | Producing exact field obligations |
| Implementations and the essential mathematical proofs | Deriving routine compatibility and composing proofs |
| A generic client/theorem with its actual assumptions | Inferring pinned dictionaries and relational rewrite contexts |
| The intended observation boundary | Reporting conditional transformation opportunities |

Defining this class does not automatically seal a representation, equip every
raw function with a certificate, or register a global equality for its carrier.
For this first showcase, explicit parameters and a requested relational derivation
are enough. Opting the class into an automatic semantic-interface surface is a
separate convenience to validate against this explicit version.

The mathematical content is small: this interface describes an associative,
commutative, idempotent operation modulo an equivalence. It is expressed as
a composition of reusable algebraic law classes in this revised sketch. The name `Mergeable`
is chosen here because it explains the program the new user wants to write.

## 8. Grounding and next probe

Existing Heather classes are ordinary parameterized records with proof fields.
Operation indexing and `Equivalence` already provide the underlying pattern.
The new pieces in this sketch are the relation-indexed combined interface,
relational calculation, generation requests, and the class-field obligation UX.
The relation notation is illustrative; `same(x,y)` is the explicit fallback.

The next manual probe should construct the list instance and the exact
`merge_twice` proof, with explicit compatibility in its last step. The automatic
version should emit the same kind of checked term. Separately verify an
unfinished field's goal display; a counterexample searcher is optional.

Owners: [relation-indexed algebra](../../issues/relation-indexed-algebra.md),
[setoid generation](../../issues/setoid-auto-lifting.md), and
[proof-opportunity diagnostics](../../issues/ai-facing-tooling.md).


## 9. Concise constraints and composition syntax

The explicit theorem header above can become:

```heather
theorem merge_twice<A: Mergeable(same as ≈, merge as ⊔)>(
    state, incoming: A):
    (state ⊔ incoming) ⊔ incoming ≈ state ⊔ incoming
{
    // Same calculation using A.assoc and A.idem.
}
```

Agreed meaning (implementation pending): `same as ≈` and `merge as ⊔` introduce implicit index binders.
Their types come from Mergeable's index declarations; the notation belongs to
those binders. The class dictionary is a solver parameter over the introduced
indices, just as for an existing empty constraint slot. The relation and
operation remain real parameters of the elaborated theorem.

A bare index name keeps its current linked-reference meaning. In particular,
an unknown name in a reference position does not become an implicit declaration.
Duplicate introduced names or symbols should fail, with explicit binders as
the fallback. Dependency ordering must respect the class index telescope.
Call sites infer indices from arguments/expected goals when possible; an
unresolved or ambiguous index requires an explicit choice, never registry guessing.
This proposed form differs from decorating a reference with `as`: it makes the
slot a declaring occurrence. See the [binder follow-up](../../issues/constraint-index-binder-introduction.md).

Decision from user review: retain `extends` for simplicity. A colon parent
list and an expression such as `Equivalence + Commutative + { extra fields }`
were considered; neither is needed for this round. A composition expression
would require its own precise dictionary/field-sharing semantics, not merely
an appealing operator spelling.

A child provides its parent evidence; independently found parent proofs do
not silently assemble a new child. Tagged parent dictionaries still distinguish
repeated law interfaces at different operation/relation indices. These
constraints remain owned by class composition. Extra user fields remain in
the ordinary class body.
