# The same set mathematics on a branching representation

The [abstract client](showcase/finite_set_client.hthr) is unchanged. Its union,
image, update, and selected-element operations now have a second implementation:
[`tree_finite_set.hthr`](../lib/std/tree_finite_set.hthr). The
[tree client](showcase/finite_set_tree_client.hthr) instantiates the existing
theorems and dependent functions.

## What is different about this representation?

`SetTree<A>` has three constructors: an empty tree, a singleton leaf, and a node
joining two trees. Union constructs a node. Image recursively maps both
branches. Membership at a join is a choice of membership in either branch;
membership at a leaf is equality with its value.

This implementation imports no list module. Its laws come from rearranging
membership evidence and induction on the branching tree. In particular,
associativity moves nested choices between the two tree shapes. Image
membership recovers a source witness from either branch. The list backend's
append and map theorems do not prove these laws for it.

The representation permits empty branches, repeated members, and arbitrary
nesting. All trees are finite by construction. It makes no balancing,
deduplication, or complexity guarantee and requires no equality decider.

## What does a client get for free?

The existing `union_twice`, `extend_union`, and `image_fusion` proofs apply by
selecting `SetTree<A>` and `tree_operations<A>`. The existing `move_selected`
and `image_selected` functions likewise transport elements carrying membership.
No tree cases occur in those abstract proofs or functions.

For example, the tree-specific entry point for receiving an update twice is:

```heather
theorem tree_receive_duplicate<A>(known, incoming: SetTree<A>):
    TreeSame(tree_union(tree_union(known, incoming), incoming), tree_union(known, incoming))
{ union_twice<A, SetTree<A>>(known, incoming, ops := tree_operations<A>) }
```

The header fixes a representation. The proof comes from the unchanged abstract
client. That is the useful representation-independence claim here; concrete
call sites still select their implementation explicitly.

The selected-element wrappers carry a pinned `FiniteSets` constraint. Their
result type does not mention union or the chosen set relation, so it cannot
select every index required by the abstract function. A concrete caller gets
the pinned dictionary from the registered backend. This is a useful reason to
consider smaller capability requirements for such functions in future;
guessing an otherwise unused operation from the carrier would be ambiguous.

## Switching implementations has proofs too

[`tree_list_set_transfer.hthr`](../lib/std/tree_list_set_transfer.hthr) connects
the two implementations after each has independently established its laws:

- Enumeration preserves and reflects membership, hence semantic equality.
- Building a tree from a list preserves membership.
- Both round trips preserve the represented set.
- Enumeration commutes with image semantically, including heterogeneous images.
- A selected tree member becomes a selected list member with the same value.

The [transfer showcase](showcase/finite_set_backend_transfer.hthr) proves that
performing an image update on trees and then enumerating agrees with performing
the corresponding update on lists. It also checks that a selected member's
value survives conversion by native equality.

Round trips intentionally have semantic conclusions. Turning the singleton
`Item(0)` into a list and back produces `Join(Item(0), Vacant)`. The showcase
proves that these trees are semantically equal and not natively equal. It also
proves that observing the root constructor does not preserve `TreeSame`.
No theorem silently identifies the tree shapes or their membership evidence.

## What this suggests for author automation

The author work has two distinct parts. Generic union laws rearrange `Or`
evidence. Representation-specific image proofs recurse over constructors and
build or recover witnesses. Both are plausible automation customers, but they
need different capabilities: connective proof search versus compositional
induction and transfer of witness-bearing evidence.

A useful next automation request would name an operation and ask for its
membership characterization or compatibility proof. Its output should be an
ordinary checked theorem, with missing constructor cases or laws exposed as
obligations. The second backend gives that work concrete examples without
requiring new surface syntax in this round.

## Verification

The final plain Furnace suite passed: **2,413 passed, 0 failed, 5 ignored**.
Both new showcase entry points passed standalone CLI checking under a 4 GiB
address-space limit and a 120-second CPU limit. The original `finite_set.hthr`
interface and `finite_set_client.hthr` are byte-for-byte unchanged from the
preceding round.
