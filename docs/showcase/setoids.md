# Setoids: choose equality once

The setoid rounds, in order: the abstract finite-set client, a second backend under it, the rationals as the first arithmetic client, and the reading list behind the transfer work. Each section was its own doc until 2026-11-15.

- [Choose equality once, then write ordinary set mathematics](#choose-equality-once-then-write-ordinary-set-mathematics)
- [The same set mathematics on a branching representation](#the-same-set-mathematics-on-a-branching-representation)
- [Rationals as the setoid round's first arithmetic client](#rationals-as-the-setoid-rounds-first-arithmetic-client)
- [Setoids, lifting, and relational transfer: reading guide](#setoids-lifting-and-relational-transfer-reading-guide)

## Choose equality once, then write ordinary set mathematics

This round builds a substantial connected setoid experience:

- [`finite_set.hthr`](../../lib/std/data/set/finite_set.hthr) is the author-facing semantic interface.
- [`list_finite_set.hthr`](../../lib/std/data/set/list_finite_set.hthr) supplies its list implementation.
- [`finite_set_client.hthr`](finite_set_client.hthr) develops the abstract mathematics.
- [`finite_set_list_client.hthr`](finite_set_list_client.hthr) applies that mathematics to lists and checks the representation boundary.

The abstract client imports no list implementation. Its carrier `S` could have
another representation; its proofs consume the chosen relation and laws.

### The user experience

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

### What the author supplies

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

### Two language improvements driven by the client

#### Relational calculation

`calc` now accepts homogeneous `≈` chains. The symbol has the declaration's
ordinary local meaning. Generated calls to `relation_props::relation_step`
consume `Transitive` evidence; `relation_exact` checks the final step. Every
written endpoint is checked, including in a one-step chain. No representative
identity, reflexivity assumption, or quotient elimination is inserted.

Clients import `relation_props` for these ordinary proof constructors. Existing
`=` calculation behavior is retained. Mixing `=`/`≈` or introducing order
chains remains separate work requiring the corresponding composition rules.

#### Complete scoped dictionaries

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

### Image compatibility without per-proof plumbing

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

### Representation access has a clear boundary

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

### Remaining distance from the ideal

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

### Verification

The final plain Furnace suite passed: **2,411 passed, 0 failed, 5 ignored**.
Both showcase entry points also passed standalone CLI checking with a 4 GiB
address-space limit and a 120-second CPU limit. Regression tests cover whole
client files, relational calculation refusals, scoped projection boundaries,
and ambiguous family certificates with an explicit-proof repair.

The calculation and scoped-projection issues are closed. The broader finite-set
roadmap and dependent dictionary performance issue remain open.

## The same set mathematics on a branching representation

The [abstract client](finite_set_client.hthr) is unchanged. Its union,
image, update, and selected-element operations now have a second implementation:
[`tree_finite_set.hthr`](../../lib/std/data/set/tree_finite_set.hthr). The
[tree client](finite_set_tree_client.hthr) instantiates the existing
theorems and dependent functions.

### What is different about this representation?

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

### What does a client get for free?

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

### Switching implementations has proofs too

[`tree_list_set_transfer.hthr`](../../lib/std/data/set/tree_list_set_transfer.hthr) connects
the two implementations after each has independently established its laws:

- Enumeration preserves and reflects membership, hence semantic equality.
- Building a tree from a list preserves membership.
- Both round trips preserve the represented set.
- Enumeration commutes with image semantically, including heterogeneous images.
- A selected tree member becomes a selected list member with the same value.

The [transfer showcase](finite_set_backend_transfer.hthr) proves that
performing an image update on trees and then enumerating agrees with performing
the corresponding update on lists. It also checks that a selected member's
value survives conversion by native equality.

Round trips intentionally have semantic conclusions. Turning the singleton
`Item(0)` into a list and back produces `Join(Item(0), Vacant)`. The showcase
proves that these trees are semantically equal and not natively equal. It also
proves that observing the root constructor does not preserve `TreeSame`.
No theorem silently identifies the tree shapes or their membership evidence.

### What this suggests for author automation

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

### Verification

The final plain Furnace suite passed: **2,413 passed, 0 failed, 5 ignored**.
Both new showcase entry points passed standalone CLI checking under a 4 GiB
address-space limit and a 120-second CPU limit. The original `finite_set.hthr`
interface and `finite_set_client.hthr` are byte-for-byte unchanged from the
preceding round.

## Rationals as the setoid round's first arithmetic client

Date: 2026-10-10. The setoid area was paused on 2026-09-05
([setoid-roadmap-and-resumption](../../issues/setoid-roadmap-and-resumption.md))
until a real client asked for it. This round resumes it with the client the
roadmap's own resumption rule names "a mathematical representation already
needed elsewhere": unreduced rationals, the first step toward the real-number
probes ([regular-cauchy-reals](../../issues/regular-cauchy-reals.md),
[constructive-ordered-field-interface](../../issues/constructive-ordered-field-interface.md)).

- `lib/std/pos.hthr`: positive naturals, positive by construction, and
  cancellation of an `Int` factor by a `Pos`. Deleted 2026-10-14: `Rat`'s
  denominator is now `Pos<Nat>` binder sugar and the cancellation lemmas live
  in `rat.hthr` (docs/library/positivity-evidence-design.md §14).
- [`lib/std/num/rat.hthr`](../../lib/std/num/rat.hthr): `Rat`, its equality `≈`, the
  respectful operations, and the ring, order, field and embedding laws modulo
  `≈`.
- [`docs/showcase/rat_client.hthr`](rat_client.hthr): a client that
  never looks inside a fraction.
- `crates/elab/tests/lib_std_rat.rs`: closure, the law kit by name, and the
  negative controls.

### What a client writes

```heather
theorem mul_inv_cancel(x, y: Rat, nonzero: ¬(x ≈ Rat::zero())): (y * x) * x.inv() ≈ y {
    calc {
        (y * x) * x.inv() ≈ y * (x * x.inv()) := Rat::mul_assoc(y, x, x.inv()),
        ≈ y * Rat::one() := rel_cong(Rat::mul_inv(x, nonzero)),
        ≈ y := Rat::mul_one(y),
    }
}
```

Read it as: regroup the product, replace `x · x⁻¹` by one inside the
surrounding product, and drop the one. Nothing new was needed in the language
for this. The pieces the finite-set rounds built carry over to a concrete
carrier unchanged:

- `designation ≈ at Rat := Rat::Same`, beside `+`, `*` and prefix `-`, gives
  the symbols their meaning at `Rat` only.
- `instance Equivalence<Rat>(Rat::Same)` is what `calc` uses to join `≈` steps
  (`relation_step`). It is also what `relation_step(Rat::Same, …)` resolves
  when called directly.
- `instance Respects2<Rat, Rat, Rat>(Rat::Same, …, Rat::add)` (and the one for
  `mul`) is what `rel_cong` finds when it lifts a step through `+` or `*`.
- `Semigroup` and `Commutative` from `algebra_rel` are registered for both
  operations, so generic relation-indexed clients apply at `Rat`.

### The representation

`Rat` is `{ num: Int, den: Pos }` and `Pos` is `{ pred: Nat }`, standing for
`pred + 1`. A denominator therefore cannot be zero. No proof field rides
along, so neither operations nor equality ever compare proofs. Nothing is
reduced: there is no gcd, no normal form and no non-structural recursion.

`x ≈ y` is `x.num * y.den.int() = y.num * x.den.int()`. Representation
identity stays available and is strictly finer. The showcase proves `1/2 ≈
2/4` by `refl` (cross-multiplication computes on closed fractions), and
proves `1/2 ≠ 2/4`. It also proves that no theorem can make the denominator
respect `≈`, because `2/2 ≈ 1/1`. That is setoid-core-api's "denominator
extraction must fail as an invariant observation", as a theorem.

Transitivity is the only place where the cross-multiplication equality needs
something beyond rearrangement: the middle denominator has to be cancelled.
`Int::mul_cancel_pos_r(x, y, p: Pos, h: x * p.int() = y * p.int())` does that.
Taking a `Pos` means the integral-domain side condition is discharged by the
type. The order counterpart, `Int::mul_le_cancel_pos_r`, carries `≤`
transitivity.

`inv` is total, with `0⁻¹ = 0`. The field law `x * x.inv() ≈ 1` takes
`¬(x ≈ 0)`, and the test checks that both the hypothesis-free statement and
`0 · 0⁻¹ ≈ 1` are refused. `inv_respects` covers the zero case too.
(Since then the total one is `Rat::recip`, and `Rat::inv`, written `x⁻¹`,
takes apartness from zero: docs/library/inverse-power-notation-design.md.)

### Where the proof text went

About a third of `rat.hthr` is commutative-ring rearrangement of integer
products. That covers `cross_term` and `add_respects`, `add_assoc`,
`distr_monomial` and `mul_add_distr`, and the shuffles in `same_trans`. The
setoid layer itself is small: the equivalence, the instances and each
`*_respects` statement are a few lines each.

The pattern that kept the rearrangement tolerable was to:

1. expand both sides by distributivity;
2. prove each pair of monomials equal with `mul_assoc`, `mul_comm` and the new
   `Int::mul_shuffle` / `Int::mul_right_comm`;
3. let `omega` do the linear bookkeeping, treating each product as an atom.

`cong` by anti-unification (no written motive) carried every
"rewrite this factor" step in the `calc` chains.

### What the client exposed

Each item below has an owner.

1. **No commutative-ring normalizer** ([ring-normalization](../../issues/ring-normalization.md)).
   Every law past the identity-shaped ones is a hand-written monomial match.
   Distributivity needed a seven-factor monomial lemma. Reals will multiply
   this: every Cauchy-modulus estimate is a polynomial identity or
   inequality. *Since 2026-10-12 the laws are one `ring` call each
   ([ring-normalization-design](../tactics/ring-normalization-design.md)); the
   rearrangement described above is history.*
2. **`omega` does not see through a defined proposition**
   ([omega-unfolds-defined-propositions](../../issues/omega-unfolds-defined-propositions.md)).
   A hypothesis `h: x <= y` at `Rat` is `Rat::Le(x, y)`, and omega skips it.
   So does a goal `x ≈ y`, and a `Pos::val(…)` atom that computes to `Succ(…)`.
   Most `omega` calls in `pos` and `rat` first restate the goal or a
   hypothesis in its unfolded form with a typed `let`. omega also
   skips a fact built as `Int::cong(λ …, p)` ("could not spell"). Those were
   rewritten as typed `cong(p)`.
3. **The elaborator accepts a hypothesis as refined by a `match` that the
   kernel then rejects**
   ([elab-match-refines-hypothesis-kernel-rejects](../../issues/elab-match-refines-hypothesis-kernel-rejects.md)).
   `match n { Zero => false_elim(h(refl)) }`, with `h: ¬Is(n)` taken before
   the match, elaborates, and then fails in the kernel with a bare
   `NotConvertible`. The workaround used throughout `inv_*` is to take the
   hypothesis after the match (`→` in the statement, `λ h =>` in each arm).
4. **Sign case splits.** `inv_parts_respects` is nine sign cases, six of them
   contradictions read off two sign lemmas. A trichotomy-on-sign view of `Int`
   would shorten it. This is not filed: one site, and the ring normalizer
   would not help it.

Things that needed nothing: `calc` over `≈` and `rel_cong` at a concrete
carrier, the `prefix -` designation inside `rel_cong`'s contexts, and
instance resolution for the relation-indexed classes. The dictionary
projection cost that the finite-set client hit
([setoid-dictionary-projection-growth](../../issues/setoid-dictionary-projection-growth.md))
did not appear: the whole module and the client check in about two seconds
cold.

### Not in this round

- Strict order, `abs`, multiplication monotonicity and Archimedean facts:
  [rational-order-completion](../../issues/rational-order-completion.md). *Done 2026-10-14:
  [rational-order-round](../library/rational-order-round.md).*
- Morphisms as respectful functions compared pointwise, and a function-valued
  representation: these remain [setoid-core-api](../../issues/setoid-core-api.md)'s
  acceptance.
- An ordered-field interface `Rat` would instantiate:
  [constructive-ordered-field-interface](../../issues/constructive-ordered-field-interface.md).
- The native-side setoid client chosen next, the x86 model's
  states-equal-except-AF relation:
  [same-defined-state-setoid](../../issues/same-defined-state-setoid.md).

## Setoids, lifting, and relational transfer: reading guide

Collected for the 2026-09-04 design discussion. This guide indexes sources and
implementation questions; decisions and acceptance criteria live in the issues.
The Lifting/Transfer paper and the refinement papers below were already present
from the data-representation discussion. They are reused, not downloaded twice.

### Primary reading

1. Brian Huffman and Ondřej Kunčar, *Lifting and Transfer: A Modular Design for
   Quotients in Isabelle/HOL* (CPP 2013).
   [Local PDF](../papers/lifting-transfer-huffman-kuncar-cpp2013.pdf) ·
   [Author-hosted source](https://www21.in.tum.de/~kuncar/documents/huffman-kuncar-cpp2013.pdf).
   Read for the separation between relational theorem transfer and operation
   construction, and for a common treatment of quotients and subtypes. Inspect
   which construction steps need representation maps or logical assumptions
   before adapting the design to Heather.

2. Matthieu Sozeau, *A New Look at Generalized Rewriting in Type Theory*
   (Journal of Formalized Reasoning 2(1), 2009; published online 2010).
   [Local author preprint](../papers/generalized-rewriting-sozeau-2009.pdf) ·
   [Author-hosted source](https://sozeau.gitlabpages.inria.fr/www/research/publications/A_New_Look_at_Generalized_Rewriting_in_Type_Theory.pdf) ·
   [Publication](https://doi.org/10.6092/issn.1972-5787/1574).
   Read for compositional compatibility proofs, higher-order rewriting,
   polymorphism, and subrelations. Ask how much relation and certificate
   plumbing can disappear from ordinary calculation proofs.

3. Jean-Philippe Bernardy, Patrik Jansson, and Ross Paterson, *Proofs for Free:
   Parametricity for Dependent Types* (JFP 22(2), 2012).
   [Local PDF](../papers/proofs-for-free-bernardy-jansson-paterson-2012.pdf) ·
   [Author-hosted source](https://www.staff.city.ac.uk/~ross/papers/proofs.pdf) ·
   [Publication](https://doi.org/10.1017/S0956796812000056).
   Read for relational translations that produce proofs from terms in pure
   type systems. The Heather research question is per-function certified
   parametricity with explicit support for modal/contextual code and its
   observers; the paper does not establish that result for Heather.

The latter two PDFs were downloaded from the listed author-hosted sources on
2026-09-04. The existing Lifting/Transfer PDF was checked during this round.

### Adjacent references already in docs

- [CoqEAL / Refinements for Free](../papers/coqeal-refinements-for-free-cpp2013.pdf).
- [Lammich / Automatic Data Refinement](../papers/autoref-lammich-itp2013.pdf).
- [Fiat / ADT synthesis](../papers/fiat-adt-synthesis-popl2015.pdf).

These were collected by [datarepr-separation](../../issues/datarepr-separation.md).
Consult them when connecting semantic transfer certificates to implementation
refinement; this round does not re-charter executable representation synthesis.

### Work ownership and sequence

Start with the [relational core](../../issues/relational-transfer-core.md) and
[manual setoid API](../../issues/setoid-core-api.md), exercising the first
[relation-indexed algebra](../../issues/relation-indexed-algebra.md) customer.
Keep [dependent transport](../../issues/dependent-relational-transport.md) and
[subtype evidence](../../issues/subtype-transfer-and-evidence.md) as early design
stress tests rather than waiting for a complete automation stack.

[Mathematical transport](../../issues/setoid-morphisms-and-transport.md) supplies
manual constructions and comparison examples. [Proof generation](../../issues/setoid-auto-lifting.md)
then reproduces those constructions; [certified parametricity](../../issues/certified-parametricity.md)
extends its reusable relational certificates.

Agreed direction: relation-indexed algebra and compositional, kernel-checked
proof generation. Open experiments: equality notation, evidence reuse versus
squashing, and the smallest adequate dependent transport interface. No quotient
kernel extension, universal proof irrelevance, or blanket parametricity theorem
is introduced by this planning round.

