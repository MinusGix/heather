---
title: Make algebraic theories generic over their equality relation
status: open
labels: [stdlib,mathematics,algebra,setoids,design]
area: mathematics
milestone: [math-classes]
created: 2026-09-04
updated: 2026-10-20
---

Decision: reusable algebraic theory should be relation-indexed. The current
identity-based `Semigroup`/`Monoid` laws cannot describe unreduced rational
arithmetic merely by attaching respectfulness proofs to the operations.

## Acceptance

- Express equivalence laws, operation compatibility, and algebraic laws modulo
  the selected relation. Preserve operation indexing and multiple structures
  on the same carrier.
- Make identity-based theory an ergonomic specialization. Decide between a
  generalized source theory and generated companion interfaces; avoid two
  independently maintained theorem libraries.
- Demonstrate a reusable semigroup/monoid theorem on both identity-based
  arithmetic and unreduced rationals. Include inherited dictionary views and
  a higher-order consumer such as a fold.
- Minimize relation plumbing in ordinary users' code and stdlib theorems using
  inferred indices and local notation. Prototype `≈` as the conservative
  spelling and compare locally using `=` for the structure relation with a
  separate identity spelling. The latter is an open experiment, not an agreed
  global change to `=`. Diagnostics must expose the actual relation and detect
  ambiguity; a carrier alone must not choose it.
- Record migration cost against existing theorem statements and dictionaries,
  not just the shortest new class declaration.

## What it assumes from elsewhere

- **[[setoid-core-api]]** owns explicit setoid and respectfulness evidence.
- **[[algebraic-theory-composition]]** owns canonical theory composition.
- **[[setoid-morphisms-and-transport]]** owns moving laws between presentations.

## Dictionary coherence stress test

The finite-set design exposed a consequence of relation-indexed laws: units
are unique modulo the relation, not necessarily by identity. Unreduced rational
zero represented as 0/1 or 0/2 is a control. Keep the exact selected parent
dictionary during inheritance; do not merge independently built dictionaries
or replace their relevant proof/data fields merely because they correspond
semantically. Explicit structure correspondence is separate from canonical
instance registration. **[[inherited-field-override-owes-conversion]]** owns the
existing override diagnostic; this issue owns the relation-indexed policy.

**[[finite-set-client-design]]** supplies a raw-fold customer for an idempotent
commutative monoid, contrasted with a duplicate-free fold needing weaker laws.

## Author-facing showcase

`docs/showcase/your-own-thing-with-laws.md` teaches the explicit pattern through
`Mergeable<A>(same, merge)`: equivalence, compatibility, associativity,
commutativity, and idempotence. A repeated-delivery theorem specializes to Nat
maximum under identity and list append under equality of members.

Use it as a small manual probe of defining one's own law-bearing interface.
It need not create a competing algebra hierarchy: after validating the user
experience, compose/alias the appropriate reusable law classes. Ordinary field
goal display is required; counterexample search is not a dependency.

## Named laws and class composition surface

The user-authored showcase now composes named `Associative`, `Commutative`,
`Idempotent`, and `Respects2` interfaces instead of restating their fields in
Mergeable. Index the algebraic laws by both relation and operation; recover
identity-specialized conveniences without duplicating theorem libraries.
Respectful predicates and evidence-bearing wrappers must share their definition.

Decision: retain `extends` for simplicity, with canonical/tagged parent
dictionary semantics from **[[algebraic-theory-composition]]**. Colon syntax
and an algebraic composition expression were considered but are not work for
this round. Additional user-defined fields remain supported. Named laws allow
clients to request only the facts they use.

**[[constraint-index-binder-introduction]]** owns the compact user-proposed
`Mergeable(same as ≈, merge as ⊔)` constraint form. The showcase's explicit
baseline now uses `A: Mergeable(same, merge)` and `A.assoc`/`A.idem`.

## Completed first implementation slice

**[[manual-mergeable-round]]** completed the first bounded implementation and
verification: named relational laws, composed Mergeable, and a generic list
instance. The broader migration and API decisions remain here.

## Author law instances directly, then compose explicitly

User preference from review of the manual round: a theorem whose primary role
is to fill a standard law field can be authored directly in that law instance.
For example, define Reflexive/Symmetric/Transitive for SameMembers with inline
proofs, explicitly declare an empty Equivalence instance, then declare the
operation laws and an empty Mergeable instance. Keep useful independent helper
lemmas as ordinary theorems; do not force every lemma into class resolution.

The existing composition mechanism already supports parent-first assembly;
the explicit composite declaration is still required and must reuse the exact
selected evidence. This is not permission for search to infer arbitrary child
instances from matching parents. Probe the generic List case, exact parent-proof
reuse, both authoring orders, and useful law projections before migrating the
landed instance. Do not add duplicate registrations alongside the existing
child-first instance.

`docs/showcase/your-own-thing-with-laws.md` records this alternative authoring
style. **[[algebraic-theory-composition]]** owns its underlying dictionary rules.

## Log

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-04: Added canonical dictionary and fold capability probes from the finite-set client design.
- 2026-09-04: Added a user-authored Mergeable showcase with concrete implementations, one generic theorem, and unfinished-field feedback.
- 2026-09-04: Revised the showcase around named law composition and carrier constraints; recorded colon composition and implicit index introduction as surface candidates.
- 2026-09-04: User selected existing `extends` syntax and agreed the declaring-slot rule for named implicit indices; no class-composition syntax change is planned.
- 2026-09-04: **[[manual-mergeable-round]]** completed with a checked showcase and full-suite validation; the full identity-hierarchy migration remains open here.
- 2026-09-04: Recorded the user-preferred individual-law instance authoring style and explicit composite assembly; generic migration remains a follow-up probe.
- 2026-09-05: [[positive-subtype-manual-round]] adds the relation-indexed Semigroup composition and makes Mergeable extend it; the positive-natural customer reuses its laws through value-based comparison.
- 2026-10-10: `Rat` (lib/std/rat.hthr) registers `Semigroup` and `Commutative` from `algebra_rel` for both `+` and `*` modulo `Rat::Same`. It is the first concrete arithmetic carrier of the relation-indexed hierarchy. A relation-indexed monoid, group or ring would let it state units and inverses as instances too.
- 2026-10-15: Numerals at `Rat` are blocked on `algebra_rel::Semigroup` sharing its name with `algebra::Semigroup`: [[rat-numerals-and-semigroup-clash]].
- 2026-10-20: The relational semigroup is now `SemigroupRel`, so a module imports `algebra` and `algebra_rel` together ([[rat-numerals-and-semigroup-clash]]); siblings follow the suffix.
- 2026-10-20: [[semiring-ring-structure-api]] adds `MonoidRel`, `CommMonoidRel` and `GroupRel` to `algebra_rel` and the two-operation layers in `lib/std/semiring.hthr`, with `Rat` a `CommRing` under `Rat::Same` and `Nat`/`Int` under `RelId` (`designation ≈ at Nat/Int := RelId`, so identity carriers state the generic theorems with `=`).
