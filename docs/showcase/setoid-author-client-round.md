# Choose equality once, then write ordinary set mathematics

This round builds a substantial connected setoid experience:

- [`finite_set.hthr`](../../lib/std/data/set/finite_set.hthr) is the author-facing semantic interface.
- [`list_finite_set.hthr`](../../lib/std/data/set/list_finite_set.hthr) supplies its list implementation.
- [`finite_set_client.hthr`](finite_set_client.hthr) develops the abstract mathematics.
- [`finite_set_list_client.hthr`](finite_set_list_client.hthr) applies that mathematics to lists and checks the representation boundary.

The abstract client imports no list implementation. Its carrier `S` could have
another representation; its proofs consume the chosen relation and laws.

## The user experience

A header chooses the interface and local mathematical notation:

```heather
theorem union_twice<A, S: FiniteSets<A>(≈, ⊔, ops)>({ops: SetOperations<S, A>}, xs, ys: S):
    (xs ⊔ ys) ⊔ ys ≈ xs ⊔ ys
{
    calc {
        (xs ⊔ ys) ⊔ ys ≈ xs ⊔ (ys ⊔ ys) := S.assoc(xs, ys, ys),
        ≈ xs ⊔ ys := rel_cong(S.idem(ys)),
    }
}
```

Read this as: combine two collections, then add the second one again; the
result represents the same set. Associativity exposes the repeated collection,
and congruence applies idempotence inside the surrounding union. Transitivity
and the context certificate are supplied by the existing laws.

The client also develops:

- Right identity, both algebraically and by membership/extensionality.
- Four-way union rearrangement.
- Image distribution, duplicate-insensitivity, composition, and fusion.
- An extension operation adding the image of the current set.
- Extension over union, its identity/empty cases, and stability under a supplied image-stability premise.
- Compatibility of user-defined expressions, including nested image contexts.
- Selection, transport, and imaging of an element carrying abstract membership.
- Preservation of existing members and introduction of mapped members during an update.

The stability hypothesis is explicit: arbitrary repeated image extension is
not idempotent. Nothing silently adds that assumption to make the theorem pass.

## What the author supplies

`FiniteSets<S,A>(same, union, ops)` extends `Mergeable<S>(same, union)`
with membership/image laws. A small `SetOperations<S,A>` value supplies empty,
image, membership, and singleton. The laws connect their meaning:
extensionality, empty/union/singleton membership, and an existential description
of image membership.

Image means an actual image of members. The list backend proves the reverse
membership direction by recovering a source element and transporting its
membership before rebuilding the mapped membership proof. It also supplies
map/append and map composition laws.

Equality, union, and the operations value are indexed choices. The current
header explicitly binds the implicit `ops` parameter; clients write `ops.image`
and project laws as `S.image_union`. Multiple local dictionaries offering the
same law make the shorthand ambiguous; explicit dictionary projection chooses
one. Calls between abstract client theorems infer the supplied operations.

This separation also matters for performance. A flat dictionary exceeded the
4 GiB test limit at `empty_right`. A tagged operations parent reached later
membership proofs but still exceeded that limit. Making operations a value
index let all 19 abstract declarations check, with the test reaching the
backend in about four seconds. The underlying cost of large dependent
dictionaries remains tracked in
[dictionary projection growth](../../issues/setoid-dictionary-projection-growth.md).

## Two language improvements driven by the client

### Relational calculation

`calc` now accepts homogeneous `≈` chains. The symbol has the declaration's
ordinary local meaning. Generated calls to `relation_props::relation_step`
consume `Transitive` evidence; `relation_exact` checks the final step. Every
written endpoint is checked, including in a one-step chain. No representative
identity, reflexivity assumption, or quotient elimination is inserted.

Clients import `relation_props` for these ordinary proof constructors. Existing
`=` calculation behavior is retained. Mixing `=`/`≈` or introducing order
chains remains separate work requiring the corresponding composition rules.

### Complete scoped dictionaries

Type projections can use a complete local multi-parameter class dictionary,
including a tagged parent preserving the primary carrier. Thus `S.image_union` works
under `FiniteSets<S,A>` even though the subject `S` alone cannot infer `A`.
Missing type arguments are not guessed from global instances. An unrelated
carrier, a shadowed dictionary name, or competing choices cannot silently
supply the operation.

Tagged parent traversal follows recorded class paths and ordinary checked
field projections. It does not identify differently indexed parent dictionaries.
Reordered primary carriers and unsupported parent paths still require explicit
projection rather than speculative argument inference.

## Image compatibility without per-proof plumbing

When congruence encounters an operation family applied to a fixed parameter,
such as `image(f, xs)`, it can apply that parameter to a field of a local
dictionary and test the result at the exact compatibility goal. For this
interface, `image_respects(f)` is the matching certificate.

The search examines at most 64 fields, applies only one argument, and kernel
checks candidates. It interprets no field names and unfolds no source operation
to infer its semantic meaning. An explicit local certificate takes precedence.
Multiple distinct matching candidates or an exhausted search leave the ordinary
compatibility obligation; supplying a chosen proof resumes normal checking.

This removes the previous `let compatible = S.image_respects(f)` bridge in
ordinary image-context proofs. It is a bounded use of supplied laws, not a
blanket parametricity theorem or a complete proof search engine.

## Representation access has a clear boundary

The concrete client can still use `list_len`. It proves that length does not
respect `SameMembers` by comparing `[0,0]` with `[0]`. Those representations
are related as sets and are not equal as lists. The abstract client has no
list carrier to inspect.

The boundary comes from writing the generic client against the interface.
This does not introduce a module-sealing system or prevent concrete code from
choosing representation-sensitive operations intentionally.

Membership evidence remains relevant. The selected-element operations use the
interface's membership implications; they do not identify stored evidence.
The [earlier transport round](element-transport-round.md) supplies the
occurrence-sensitive counterexample for that distinction.

## Remaining distance from the ideal

The current interface uses native equality for elements and image by
endofunctions `A → A`. The backend's image-compatibility proof is heterogeneous
in element types, but exposing cross-carrier image in the abstract interface
needs a related family of set carriers. Element setoids are a further explicit
relation choice, not something silently supplied by the outer set relation.

The abstract laws describe extensional set algebra. The list implementation is
finite, but the interface does not yet carry a finiteness/enumeration witness;
these laws alone also admit infinite-set models. No cardinality, equality
decider, deduplication, or canonical representation follows from them.

A class-bound header is still repeated in generic declarations. Mixed-relation
calculations, normalization of whole algebraic expressions, and automatic
discovery of arbitrary inherited theorems remain outside this implementation.
The named-index syntax proposal and anonymous-predicate inference issue remain
separate; neither is needed to disguise an unresolved obligation here.

## Verification

The final plain Furnace suite passed: **2,411 passed, 0 failed, 5 ignored**.
Both showcase entry points also passed standalone CLI checking with a 4 GiB
address-space limit and a 120-second CPU limit. Regression tests cover whole
client files, relational calculation refusals, scoped projection boundaries,
and ambiguous family certificates with an explicit-proof repair.

The calculation and scoped-projection issues are closed. The broader finite-set
roadmap and dependent dictionary performance issue remain open.
