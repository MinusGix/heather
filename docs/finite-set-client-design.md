# Finite sets: design from client code

Status: exploratory design, 2026-09-04; no implementation or syntax freeze.
Owner: [finite-set-client-design](../issues/finite-set-client-design.md).

Start with [the idealized client](showcase/finite-sets-idealized.hthr), then
argue about the certificates it needs. The code deliberately does not check.
For the smaller teaching surface developed next, start with
[three small experiences](three-small-transfer-experiences.md).

Its acceptance target is ordinary mathematical programming with visible
semantics and mostly inferred proof plumbing. This is a candidate design,
not a promise that the generator already supports these constructions.

## 1. The client experience

The main client is just:

```text
extend(f, xs) = xs ∪ image(f, xs)
```

It should get a conditional compatibility theorem automatically. A calculation
showing that `extend` preserves union should use the image and union laws;
rewriting `xs ∪ xs` inside `extend` should not need a new congruence lemma.

An arbitrary `f` is not assumed compatible. The sketch writes a real parameter
`hf: Respects(E, E, f) := derive()`. At a call site it can come from local
evidence, a registered theorem, or successful analysis of the actual function.
The definition and its certificate remain conditional on that parameter.
Adding a premise to an existing client's contract is a visible source change,
not an automatic response to a failed proof.

The proposed `within finite_sets<A>(E, eq)` block gives short local names for
the chosen carrier, relation, and certified operations. It expresses context
sharing, not another class system. An explicit version must always be possible:
`FiniteSet<A>(E)`, `SetEq(E, xs, ys)`, `image(E, F, f, hf, xs)`, and ordinary
dictionary parameters. Actual argument order remains open.

Keep `=` as identity and `≈` as the locally supplied relation in this sketch.
The compiler must refuse ambiguous relation indices rather than nominate a
global relation for `List<A>`. This choice lets us assess inference separately
from the more disruptive equality-notation experiment.

## 2. What counts as the same finite set?

Start with an element equivalence `E : A → A → Type`. On list representatives:

```text
Mem(E, a, [])       = False
Mem(E, a, b :: bs)  = E(a,b) ∨ Mem(E,a,bs)
SetEq(E, xs, ys)    = ∀ a, Mem(E,a,xs) ↔ Mem(E,a,ys)
```

These are schematic equations, with Heather's proof-relevant disjunction and
Iff. Equivalence of membership propositions supplies maps between witnesses,
not equality of those witnesses. No equality decider is needed to state these
definitions, or to concatenate lists and prove it implements union.

Two list views must remain distinct: pointwise list relatedness preserves
shape and length; `SetEq` forgets ordering and repetition. A parametricity
theorem for list map gives useful infrastructure but does NOT, merely by
instantiating its element relation, become the finite-set map theorem.
The library needs a theorem that map preserves `SetEq` under respectful maps.
That theorem is then the reusable rule the client generator consumes.

There are two abstraction questions:

- **Semantic certification:** is a particular function compatible with this
  view? This can be proved even when its implementation inspects lists.
- **Interface restriction:** is a generic client written using only the given
  interface? Start by parameterizing over an abstract carrier and operation
  dictionary. Current module imports are not an abstract sealing mechanism.

Neither a type alias nor a wrapper around a list makes arbitrary functions
respectful. Generated client certificates are the semantic guarantee.
Sealing/visibility can be designed separately if a concrete API needs it.

## 3. The smallest interface and what can be derived

Specify operation signatures, their compatibility obligations, and observation
laws. For this example the interface has empty, singleton, union, membership,
and image between element views. Image is a cross-interface operation indexed
by source and target views; it need not be forced into one monomorphic record.
Full polymorphic/higher-kinded interface packaging is not a prerequisite.

| Operation | Compatibility obligation | Semantic law supplied by implementation |
| --- | --- | --- |
| empty | Self-related at `SetEq` | No element is a member |
| singleton | `E ⇒ SetEq(E)` | Membership corresponds to `E(a,b)` |
| union | `SetEq ⇒ SetEq ⇒ SetEq` | Membership is the disjunction of input memberships |
| membership | `E ⇒ SetEq ⇒ Iff` | Defines the observable proposition |
| image(f) | `SetEq(E) ⇒ SetEq(F)`, assuming `E ⇒ F` for f | Membership corresponds to an input member whose image is F-related |
| filter(P,d) | `SetEq ⇒ SetEq`, assuming P invariant under E | Membership is original membership together with P |

Here arrows denote the heterogeneous function relator, not ordinary arrows.
The image observation law can use a relevant `Exists` witness and Iff; it
does not assert that two choices of preimage are identical. Filtering requires
a decider in addition to predicate invariance. The client must not inspect
the particular evidence returned by the decider unless separately certified.

Generating compatibility signatures from these types is plausible once the
relational interpretation is specified. Generating the membership laws merely
from operation types is not: those laws specify what the operations mean.
Similarly, assembly of a structure correspondence needs proofs that the two
implementations' operations correspond, not just self-compatibility on each.

Derive union's associative, commutative, idempotent and unit laws once from
the observation laws plus set extensionality. Parameterize client theorems
over that theory. This is smaller than transferring every concrete list proof.
An extensionality law is part of the abstract interface: membership equivalence
must imply the selected set relation, not only follow from it.

## 4. What the client certificates actually say

For fixed f, the generated result is:

```text
Respects(E,E,f) → Respects(SetEq(E),SetEq(E),extend(f))
```

A stronger two-function theorem follows from the same analysis when supported:

```text
(E ⇒ E)(f,g) →
  ∀ xs ys, SetEq(E,xs,ys) → SetEq(E,extend(f,xs),extend(g,ys))
```

Neither theorem asserts identity of `extend(f)` and `extend(g)`. The proofs
compose the image certificate and union certificate. Open proof parameters
are retained; where bodies consume them relevantly, the generated signature
must account for their relation too. In this client they are used only as
compatibility evidence, and the raw list operations do not inspect them.

For `extend_union`, the nontrivial step is ordinary union rearrangement:
`(xs ∪ ys) ∪ (fx ∪ fy) ≈ (xs ∪ fx) ∪ (ys ∪ fy)`. For
`extend_duplicate`, the generator proves compatibility of the surrounding
context. The user provides only `union_idem(xs)` as the rewrite.

Definitions built from certified operations should acquire certificates at
an explicit derivation request first. Automatic derivation at every definition
can follow once latency, expected relation selection, and output size are known.

## 5. The fold exposes a useful capability ladder

To evaluate a list representative by combining `weight(a)` in a target B,
a sufficient reusable interface is a relation-indexed idempotent commutative
monoid, with respectful weight and combining operation. Its laws explain why
equivalent raw lists have related results:

- Element compatibility handles replacement by E-equivalent representatives.
- Associativity and the unit support composition and the empty set.
- Commutativity removes dependence on enumeration order.
- Idempotence removes dependence on duplicate occurrences.

This is a convenient sufficient package, not a claim that every law is necessary
on every value of B. Specialized rules may need laws only on the generated
image or reachable accumulator values. A generator reports the premises of
the rule it tried, not a logically weakest precondition.

Raw list sum fails: `[1]` and `[1,1]` are `SetEq`-equivalent but sum to 1 and 2.
This does not mean finite sets cannot be summed. A duplicate-free enumeration
lets a commutative monoid suffice. Constructing one from arbitrary lists needs
an appropriate duplicate-removal capability (a decider for E is sufficient),
or the API can accept an already certified enumeration. Cardinality follows
by summing the constant weight 1 over such an enumeration.

Thus there are two implementations with different certificates:

```text
raw fold        + idempotence certificate → duplicate-insensitive aggregation
deduplicated fold + enumeration certificate → distinct-element aggregation
```

This distinction is also present in mathlib's separate hypotheses for ordinary
finite-set folds and idempotent image/insertion lemmas; finite-set folding
itself does not demand idempotence. See the
[Finset.fold API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Fold.html).
Heather's extra obligation here comes from the proposed raw list representation.

The list head is another instructive failure: `[a,b]` and `[b,a]` may have
unrelated heads. A compatible ordering can enable a different minimum-selection
implementation; it does not prove the existing head implementation invariant.
A predicate returning the set of permitted choices is another specification,
not an automatically synthesized deterministic selector.

## 6. A failed proof should explain the available benefit

Use structured candidate records with a concise human rendering. Example:

```text
Candidate: direct raw fold for summarize
Would enable: aggregation without a duplicate-removal pass
Known: weight compatibility; associative/commutative operation; unit
Missing: ∀ b, R(op(b,b),b)             [sufficient generic rule]
Where used: duplicate-insertion case of list/set correspondence
Alternative: certified duplicate-free enumeration, then ordinary monoid fold
Status: conditional candidate; no implementation registered
```

For an arbitrary function supplied to image:

```text
Candidate: image(f) from list map
Would enable: mapping finite sets across the specified element relations
Missing: ∀ x y, E(x,y) → F(f(x),f(y))
Available context: E, F, f and their actual local assumptions
Discharge options: supply a lemma; derive it from f; explicitly strengthen caller
```

For length-as-cardinality, show the `[a]` / `[a,a]` witness if the counterexample
facility finds and validates it. A timed-out search alone never earns the
label "refuted". Distinguish proved, missing-evidence, unsupported-analysis,
resource-exhausted, and refuted candidates.

Each candidate record should contain its exact context/goal, source location,
proposed output and conditional theorem, rule and premise dependencies, evidence
already found, assumptions/provenance, and the benefit description. A checked
conditional term `premises → certificate` is a stronger artifact than an
unverified plan; mark which is available. Proof terms over open local contexts
need the usual scoping/substitution discipline, not printed names as identities.

This extends existing obligation reporting and AI-facing search-state tooling.
It does not introduce checked declarations with open holes: outstanding
obligations remain diagnostics or candidate data. A completed proof produces
a new fully checked artifact. Reuse is valid only for matching source, relation,
dictionary and assumption dependencies; otherwise re-elaborate/recheck.

The same envelope can carry an optimization opportunity. In this example,
proving duplicate insensitivity permits removing a deduplication pass when
its only relevant consumer is that fold. If the deduplicated value also flows
to cardinality or another consumer, their observations must be preserved too.
"One fewer deduplication pass" is a structural benefit; an asserted speedup
needs a separate cost model or measurements. Semantic evidence does not prove
profitability, and the proposed rewrite is not enabled before certification.

## 7. A small, genuinely dependent client

`Element(xs) = Σ a:A. Mem(E,a,xs)` depends on the set parameter. Given
`h: SetEq(E,xs,ys)`, membership's forward map constructs `Element(ys)` from
`Element(xs)` while leaving a unchanged. This is executable transport supplied
by h, rather than a request to the kernel to identify xs and ys.

For a same-element-domain comparison, equip these fibers with the heterogeneous
relation `ElementRel(e,e') := E(e.value,e'.value)`, ignoring membership evidence.
Forward and backward transport are inverse modulo this relation. Their
composites need not be identity-equal to the original records: applying the two
membership maps need not recover the original proof term.

Two proofs h and k of set equivalence give element transports agreeing in
underlying value, hence related outputs, without equating h and k. A function
that inspects a membership witness (for example its occurrence in a raw list)
does not inherit that independence and must pass a separate compatibility test.

Repeat the example with squashed membership fields. This changes which
witness-consuming programs can be written. Compare the actual reconstruction
and checking costs before recommending a default evidence policy.

This is a first dependent success, not a general solution: it exploits explicit
membership maps. `Vector(A, cardinality(xs))` would additionally require a
cardinality implementation, a theorem that equivalent sets have equal lengths,
and the appropriate indexed transport. Keep that as a later boundary probe.

## 8. Swap implementations without claiming too much

Use lists with duplicates and duplicate-free lists as the first two carriers.
On both, semantic equality is extensional membership modulo E. The latter
stores an invariant, possibly squashed; it need not impose an order.

A decider for E can construct a duplicate-free representation from a raw list;
forgetting the invariant supplies the reverse representation map. Their inverse
laws are semantic relations, not identity of raw lists or invariant proofs.
Both implementations must satisfy the observation laws and the cross-carrier
operation correspondence. Then the generic `extend_union` theorem applies,
and the client correspondence theorem relates the two implementations.

Sorted canonical lists can be a separate stronger implementation. Sorting and
deduplicating modulo a nontrivial E does not automatically choose the same raw
element representative. A claim of unique identity-level normal forms needs
extra representative-normalization structure. Order and decidability remain
capabilities of implementations/operations, not requirements on all finite sets.

For a less expensive first executable probe, specialize E to Nat identity;
retain a nontrivial relation such as parity as a mathematical negative control
so the API cannot accidentally rely on element identity throughout.

## 9. Two broader design consequences

**Relational derivation needs a semantic interpretation environment.** Traversing
the shape of a record can produce fieldwise signatures only after choosing the
relation on each carrier and the treatment of relevant witnesses. `List<A>`
does not choose between sequence, multiset, and finite-set semantics. A finite
set view registers its operations' certificates as that explicit environment.
This is the tractable first step toward deriving correspondence for interfaces.

**Canonical dictionaries still require exact identity discipline.** Moving laws
to a relation also weakens uniqueness of data fields: two monoid units are
unique modulo R, not necessarily identical. For example, unreduced fractions
can present zero as 0/1 or 0/2. Do not merge two dictionaries merely because
their operations/units are semantically equivalent. Reuse the exact selected
parent dictionary for inheritance; prove a separate relational correspondence
when comparing independently constructed structures. Generated transfer must
not silently replace parent projections or relevant law evidence.

## 10. What is existing, proposed, and still undecided?

| Feature | Current grounding | Design gap / owner |
| --- | --- | --- |
| Ordinary function/record clients | Present in stdlib | No new core syntax needed |
| Relation laws and explicit maps | `relation_props` | [Shared relator](../issues/relational-transfer-core.md) |
| Operation-indexed dictionaries and local operator binders | Existing class/notation design | [Relation-indexed algebra](../issues/relation-indexed-algebra.md) |
| Short local finite-set view | Explicit parameters are the fallback | This showcase; avoid prematurely designing a module system |
| `derive()` and relational client certificates | Existing certifying-generator direction | [Auto-lifting](../issues/setoid-auto-lifting.md) |
| Contextual ≈ calculation | Existing identity calc is the stylistic baseline | [Auto-lifting](../issues/setoid-auto-lifting.md) |
| Whole-interface correspondence | Record/class structures supply a starting point | [Mathematical transport](../issues/setoid-morphisms-and-transport.md) |
| Conditional proof opportunities | Obligation records and search-state direction | [AI-facing tooling](../issues/ai-facing-tooling.md) |
| Element transport | Explicit membership maps | [Dependent transport](../issues/dependent-relational-transport.md) |
| Squashed membership variant | Squash exists | [Subtype evidence](../issues/subtype-transfer-and-evidence.md) |

The recommended next implementation slice is manual raw-list semantics, union,
image, the two extend theorems, and Element transport, with exact certificate
signatures. Then make automation reproduce them and shrink the idealized/real
gap. Keep deduplication and fold opportunities as the next slice, not prerequisites
for seeing whether the basic client experience works.

Validation in this round is mathematical inspection and repository/API/source
comparison, not a Heather proof check. No runnable counterpart exists yet.
Sources for the broader design are in [the reading guide](setoid-transfer-references.md).
