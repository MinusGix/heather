# Manual Mergeable: implementation record

Status: implemented and verified, 2026-09-04.

Historical record: the [proof-position round](proof-position-relational-congruence.md)
subsequently replaced the library theorem's explicit compatibility step with
`rel_cong(A.idem(incoming))`. The manual derivation below remains a comparison.

Round owner: [manual-mergeable-round](../issues/manual-mergeable-round.md).
The [realized showcase](showcase/mergeable.hthr) is checked by the
`lib_setoid_mergeable` integration target. It is the first implemented slice
of [writing your own thing with laws](showcase/your-own-thing-with-laws.md).

## What is implemented

- `std/relation_props` defines `Respectful(R,S,f,g)`, with independently
  varying input and output carriers and identity/application/composition laws.
  Existing `PreservesRelation` is definitionally its self-related specialization.
- `std/algebra_rel` defines `Respects2`, `Associative`, `Commutative`, and
  `Idempotent`, and composes `Mergeable` from those laws and `Equivalence`.
  `Respects2` wraps a nested `Respectful`, not a second compatibility formula.
- `std/list_setoid` defines `SameMembers` using existing identity-based `Mem`,
  proves its equivalence laws, and registers a generic Mergeable instance for
  append. No equality decider, deduplication, squash, or quotient is needed.
- `merge_twice` performs the two-step argument explicitly: associativity,
  followed by idempotence under the outer merge using compatibility.

The new law hierarchy is a small separate module. The identity-based algebra
module is unchanged; migration of that hierarchy remains a later round.
Lean execution-semantics imports do not gain the new law classes.

## The actual generic proof

```heather
theorem merge_twice<A: Mergeable(same, merge)>(
    same: A → A → Type, merge: A → A → A, state, incoming: A):
    same(merge(merge(state, incoming), incoming), merge(state, incoming))
{
    let laws = A::Mergeable(same, merge);
    A.rel_trans(
        merge(merge(state, incoming), incoming),
        merge(state, merge(incoming, incoming)), merge(state, incoming),
        A.assoc(state, incoming, incoming),
        laws.respects2(state, state, A.rel_refl(state),
            merge(incoming, incoming), incoming, A.idem(incoming)))
}
```

The explicit compatibility step is precisely the proof plumbing that relational
calculation should later generate. The generic theorem is already usable:

```heather
theorem receive_names_twice<A>(known, incoming: List<A>):
    SameMembers((known ++ incoming) ++ incoming, known ++ incoming)
{
    merge_twice(SameMembers<A>, append<A>, known, incoming)
}
```

The showcase supplies Boolean conjunction as a small identity control and
reuses this same theorem to prove an identity equation. This substitutes a
ready existing operation for the idealized document's illustrative Nat maximum;
implementing a maximum library was not needed to test relation specialization.

## What implementing it corrected

| Idealized convenience | Working spelling / finding | Follow-up |
| --- | --- | --- |
| `A.respects2` like every other law | `Respects2` has three type parameters; carrier-directed projection only supports a one-parameter owner. Project `A::Mergeable(same,merge).respects2` instead. | Keep explicit dictionary access; broader projection ergonomics can be considered with relation-indexed algebra. |
| `≈` calculation with contextual rewriting | Explicit `same(...)`, `A.rel_trans`, and `laws.respects2` | [Auto-lifting](../issues/setoid-auto-lifting.md) |
| Introduce indices inside the constraint | Explicit same/merge parameters still work | [Compact binder introduction](../issues/constraint-index-binder-introduction.md) |
| `(a:A) → Mem(a,xs) ↔ Mem(a,ys)` in a Type-valued body | **Closed 2026-09-17.** `(a:A) → (Mem(a,xs) ↔ Mem(a,ys))` now parses and is what `std/list_setoid` writes; the *unparenthesized* spelling still leaves the right occurrence outside the binder, which is the `↔`-is-looser-than-`→` precedence and is not a gap. | [The parser fix](../issues/iff-in-type-valued-body.md): a bracket lifts the codomain's `↔` restriction, so the parentheses group as written. |
| Partially apply a helper's explicit argument list to fill an Iff direction | Use `λ h => helper(..., h)`; partial application of those declared parameters is refused | Existing returned-function style is another possible library spelling. |
| Infer the carrier of numeral-only list arguments | Supply `<Nat>` on both the relation and the theorem used on `[0]` where inference is deferred | Explicit specialization is the current fallback. |

No kernel, parser, elaborator, or solver change was needed *by this round*.
These are findings about the source-level gap, not claims that the idealized
syntax now checks — except where a row says so: the parenthesized `↔` row was
closed by a later parser fix and `std/list_setoid` now writes the idealized
spelling.

## Evidence and boundaries

The new four-test target checks:

1. The complete realized showcase, with open list inputs, identity and
   membership instances, and the checked length-compatibility refutation.
2. A genuinely heterogeneous relation: a Nat is related to a list when it is
   a member. Successor corresponds to mapping successor over the list;
   composition and application of the shared relator preserve this evidence.
3. Named-law resolution through the Mergeable child. Its commutativity
   projection is definitionally the exact registered proof, and an open child
   dictionary supplies the corresponding parent.
4. Refusal to use the SameMembers commutativity instance at an identity goal.

The existing five relation tests also pass after the PreservesRelation
refactoring. Final verification with plain `furnace run -- scripts/test` passed:
**2,319 passed, 0 failed, 5 ignored**. The full run took 433 seconds including
warmups. Rust formatting, document links, tracker checks, and diff whitespace
checks also passed.

The checked length refutation is an ordinary theorem: applying a purported
compatibility proof to `[0,0]` and `[0]` would prove `2 = 1`, contradicting the
existing Nat inequality theorem. It is not an implemented counterexample
searcher or new diagnostic behavior.

Still owned elsewhere: arbitrary element setoids for membership, respectful
morphisms and pointwise function relations, unreduced rationals, finite-set
image/client generation, dependent transport, full algebra migration, and
automated proof-obligation reporting. This round establishes a small successful
manual construction for those later tools to reproduce.

## Following round

[Composed relational contexts](relational-context-round.md) develops the next
proof-construction layer and a separate executable showcase. The explicit
`merge_twice` proof above remains the baseline; automatic rewriting is still open.
