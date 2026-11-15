# Keep the element, change the collection

Suppose you have selected an element of a collection. Someone replaces that
collection by another representation with exactly the same members. You want
to keep using your selected value, with evidence that it belongs to the new
collection.

The [checked showcase](element_transport.hthr) expresses that directly:

```heather
record Element<A>(xs: List<A>) { value: A, member: Mem(value, xs) }

fn move_element<A>(xs, ys: List<A>, same: SameMembers(xs, ys),
    e: Element<A>(xs)) → Element<A>(ys)
{
    Element(value := e.value, member := same(e.value).mp(e.member))
}
```

The collection is part of the element's type. `SameMembers` supplies a
membership implication in each direction, so moving an element means keeping
its value and applying the appropriate implication to its membership evidence.
The lists themselves need not be equal: the concrete customer moves from
`[0]` to `[0, 0]`.

## What stays the same

`SameElement(xs, ys, e, f)` compares the values of elements belonging to
possibly different collections. Under this relation:

- Moving preserves the selected value and respects equivalent inputs.
- Moving along reflexive equivalence preserves the element.
- Two successive moves agree with moving along composed equivalence.
- Moving there and back preserves the element.
- Two proofs of collection equivalence give equivalent moved elements.

The reverse round trip follows by applying the same generic law with the
collections exchanged. These are laws under value equality, including when
both elements live in the same collection; they do not identify membership
proofs.

The small `move_property` theorem reuses an arbitrary `P(e.value)` after the
move. Its hypothesis remains explicit. This works by the computation rule
that moving preserves `.value`; no universal dependent rewrite tactic is
being introduced. Reusing the original `Element(xs)` directly at `Element(ys)`
is rejected, while the explicit move checks.

## What can still change

Membership evidence can identify an occurrence. In `[0, 0]`, membership of
zero can point to the first or second copy. The showcase defines two
transparent equivalences from `[0]` to `[0, 0]`, choosing different copies.
Their moved elements satisfy `SameElement`, but the `occurrence` function
returns zero for one and one for the other.

This gives a checked counterexample: `occurrence_cannot_ignore_membership`
refutes any claim that `occurrence` respects `SameElement`. Equivalence-witness
independence therefore holds for the selected value, while evidence-inspecting
observations may distinguish the results. Keeping the two equivalences as
functions lets the occurrence examples compute; opaque theorem bodies would
hide their evidence choices.

## Where this leaves the design

This is a successful transport through a varying dependent family, using
existing Heather records and membership maps. It complements the
[witness-bound refusal example](witness-subtype-round.md): related indices do
not automatically identify result types, but suitable structure can give an
actual map between them.

The explicit code gives future automation three concrete responsibilities:
construct the membership map application, prove its value behavior, and reuse
only observations certified compatible with the chosen relation. General
fiber interfaces, dependent-pair relation packaging, generated dependent
rewriting, and coherence for other families remain under
[dependent relational transport](../../issues/dependent-relational-transport.md).

The separate [anonymous predicate-index inference issue](../../issues/lambda-predicate-index-inference.md)
already tracks the subtype inference papercut; this round does not change it.

The concrete duplicate examples spell `<A>` or `<Nat>` where collection
literals would otherwise leave the element type undetermined. This follows
Heather's existing checking-only literal rule; the generic transport calls
with typed collection parameters need no such annotations.

## Validation

The focused setoid/subtype target passes all 49 tests. The showcase also passes
ordinary CLI checking on Furnace, with existing standard-library lint warnings.
Refusal controls reject direct reuse across collection indices, identity of
the two differently witnessed elements, and loss of a transferred property's
hypothesis. A positive explicit-move control checks the same dependent signature.

Final plain `furnace run -- scripts/test`: 2,406 passed, 0 failed, 5 ignored.
Issue lint passes for all 459 issues. This round changes no compiler or kernel code.
