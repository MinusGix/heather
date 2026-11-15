---
title: Generate relational compatibility, lifted operations, and transfer proofs
status: open
labels: [kernel,metaprogramming,design]
area: tactics
created: 2026-07-23
updated: 2026-09-05
---

Build a certifying generator over boxed code using compositional relational
proof rules. Outputs are ordinary kernel-checked terms; the generator itself
is untrusted. This develops the quotient-substitute direction without adding
an axiom equating representatives or a new kernel quotient former.

## Scope

Expose three distinct requests over a shared proof engine:

1. Certify an existing function at a requested relational signature.
2. Construct a lifted function from an explicit representation interface and
   return its definition, compatibility certificate, and useful projection or
   computation lemmas.
3. Generate a transferred theorem or structure using certified correspondences.

Start with variables, application, lambdas, registered constant/constructor
rules, and relational induction for supported recursion. Relations lift through
function and container types. Prefer registered certificates at abstraction
boundaries to repeatedly unfolding implementation bodies.

A failed structural derivation leaves a precise proof obligation; it does not
prove non-respectfulness. Representation-sensitive branching may still be
valid when branch results agree modulo the output relation. Permit manual
lemmas and resume generation after they discharge the missing step.

## Acceptance

- Reproduce the manual transport examples with kernel-checked outputs.
- Support contextual rewriting and calculation chains, including higher-order
  contexts, with inferred certificates and visible relation diagnostics.
- Include a recursive/list consumer, an opaque operation with a supplied rule,
  and a branch-sensitive function requiring a user lemma.
- Reject an invalid representative observation and report the first missing
  relational obligation for an unsupported operation.
- Cache/reuse certificates by their actual function, relation, and assumption
  parameters; measure proof size and checking cost on composed examples.
- Keep per-function parametricity derivation as a supported extension through
  [[certified-parametricity]], not a blanket assumption about all Heather code.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns the proof rules this generator emits.
- **[[setoid-morphisms-and-transport]]** owns manual mathematical constructions.
- **[[compile-typeclass-design]]** owns proof-carrying instance infrastructure.
- **[[front-end-sugar]]** owns boxed-code/view-layer ergonomics.
- **[[certified-parametricity]]** owns parametricity certificates and coverage.

## Concrete client and productive failure

**[[finite-set-client-design]]** supplies the first ideal client and contextual
calculation examples. A list-map parametricity rule for pointwise list relations
is not already a finite-set image rule: consume the library's `SetEq` theorem.

**[[ai-facing-tooling]]** owns conditional proof-opportunity records and their
benefit descriptions. Generation should report its exact missing premises,
resume/recheck after supplied evidence, and distinguish an unsupported derivation
from a refuted semantic claim. Never silently strengthen the caller's contract
or register an artifact with outstanding holes.

## Small automatic entry point candidate

For subtype operation construction, `docs/showcase/smart-subtype-inheritance.md` scopes
the first request to an explicit source operation, target signature, and
representation interface. Generate the positive-addition wrapper and its
projection theorem with registered closure evidence or resumable goals. Keep
the evidence policy explicit; do not recognize subtypes by field names.
Broader function discovery may suggest conditional signatures, but must not
silently change a requested contract or strengthen every ambient result.
Prefer a Heather metaprogram entry point receiving named or quoted source code
and the requested target; invocation syntax and inspection APIs remain design
work. Later ambient-theorem discovery/application can reuse this machinery to
adapt a selected theorem to subtype arguments and expose remaining conditions.
Explicit operation generation alone does not complete that discovery experience.

The tiny examples in `docs/showcase/three-small-transfer-experiences.md` propose
compatibility checking at declarations explicitly using a registered semantic
interface. This is a scoped UX target, not unrestricted derivation on all
functions. Retain an explicit derivation path for the first implementation and
for inspecting the raw function/certificate pair. Failure never silently adds
a premise or registers semantic eligibility without a checked certificate.

Exercise a composite whose intermediate semantic relation differs: set input,
duplicate-free enumeration modulo permutation, and Nat-valued length modulo
identity. Inferring a relation from the intermediate raw List carrier would
select the wrong requirement.

## Author-defined law interface probe

`docs/showcase/your-own-thing-with-laws.md` supplies an explicit, user-authored
`Mergeable` class. Its `merge_twice` calculation needs automatic compatibility
under a surrounding merge. Its `receive` client asks for a compositional
certificate from the supplied dictionary, with no new global relation selection.

Display the exact compatibility goal when generation stops. This states only
that preservation is not established; a stronger refutation requires a checked
witness from optional bounded counterexample search. An unfinished law field
must prevent instance registration.

## Log

- 2026-09-05: Started [[explicit-subtype-code-template]]: a context-only named
  template emission entry point and Heather templates for a binary wrapper
  and its projection certificate, with explicitly supplied closure evidence.
- 2026-09-05: [[explicit-subtype-code-template]] completed, including generated
  positive addition, its projection proof, and resumable closure obligations.
  The final Furnace suite passed (2,374 tests, 5 ignored). Body analysis,
  automatic closure discovery, and structure/theorem discovery remain open.

- 2026-07-23: Filed from foundations discussion (see [[kernel-v1-extensions]]
  log of the same date): quotients stay out of the kernel for now, setoids +
  this auto-lifting story are the plan of record.
- 2026-09-04: Expanded from the agreed relational-transfer design; implementation remains open.
- 2026-09-04: Linked the ideal finite-set client and shared proof-opportunity diagnostics.
- 2026-09-04: Recorded the narrow automatic declaration-checking candidate and the intermediate enumeration relation probe.
- 2026-09-04: Added the user-authored interface and relational-calculation probe; normal failure reporting requires no counterexample finder.
- 2026-09-04: **[[manual-mergeable-round]]** supplies a checked `merge_twice` proof with explicit transitivity and compatibility, and a realized showcase. This is the target construction for relational rewriting to reproduce; no generator landed in that round.
- 2026-09-04: The next context-construction slice adds explicit constant and dependent-on-input function application certificates, plus a self-related binary helper, in `std/relation_context`. `docs/showcase/relational-contexts.hthr` exercises nested and repeated occurrences. See `docs/showcase/relational-context-round.md`; automatic context discovery and relational calc remain open. The constructors are transparent functions so proof-relevant evidence can compute. Focused validation: 7 passed. Final plain Furnace suite: 2,322 passed, 0 failed, 5 ignored.
- 2026-09-04: Started [[bounded-relational-context-generator]]: explicit source-level context generation, structured missing-evidence goals, and isolated checking. Boxed-code/meta-layer implementation remains open.
- 2026-09-04: Started [[single-contextual-rewrite]]: recover a binder-free context from a theorem goal and named relation proof, then reuse the bounded certificate planner. Native tactic and meta-layer integration remain open.
- 2026-09-04: [[single-contextual-rewrite]] is complete for the bounded source driver: repeated/partial occurrences, checked missing obligations, and ordinary generated proof application. Full suite: 2,336 passed, 0 failed, 5 ignored. Higher-order contexts, calculation chains, native tactic integration, and the boxed-code implementation remain open.
- 2026-09-05: [[proof-position-relational-congruence]] connects supplied lemma applications to ordinary local proof goals. The first native fragment uses resolved terms and one homogeneous relation, class parent resolution, and resumable compatibility goals.
- 2026-09-05: [[proof-position-relational-congruence]] is complete for homogeneous unary/binary contexts at Type<0>. The library now uses supplied lemma applications with local law resolution and ordinary resumable goals. General relation changes, dependent/higher-order contexts, calculation chains, and boxed-code integration remain open. Final plain Furnace suite: 2,348 passed, 0 failed, 5 ignored.

- 2026-09-05: Roadmap coverage audit: [[relational-transfer-core]] owns container/higher-order relators and mixed relations; [[setoid-core-api]] owns morphisms/rationals; [[setoid-morphisms-and-transport]] and [[subtype-transfer-and-evidence]] own operation/law transfer; [[dependent-relational-transport]] owns varying fibers; [[certified-parametricity]] owns per-function parametricity. Recursion, branches, boxed-code integration, certificate reuse and cost measurement remain explicit acceptance here. Calculation chains are already covered here; newly filed [[relational-rewrite-controls]] gives reverse steps, occurrence control and mismatch explanations a concrete owner. [[relational-showcase-notation]] is the short notation round before the subtype customer.
- 2026-09-05: The notation round exposed [[relational-index-inference-from-goals]]: a concrete SameMembers conclusion does not yet determine the compact theorem's implicit indices through the current unifier. This is separate from symbolic-header parsing and from [[constraint-index-binder-introduction]].
- 2026-09-05: [[relational-showcase-notation]] completed: scoped ≈/⊔ notation and the existing implicit symbol-index header now appear in the checked showcase. Editor checks and plain Furnace suite passed (2,351 passed, 0 failed, 5 ignored). Next planned mathematical customer remains [[subtype-transfer-and-evidence]].
- 2026-09-05: Expected-goal relation/operation inference landed in [[relational-index-inference-from-goals]]; the concise list client now checks. Subtypes remain the next planned customer.
- 2026-09-05: The author/client round adds a bounded attempt to apply a fixed operation-family argument to a local dictionary field, kernel-checking the candidate at the exact compatibility goal. It aims to remove per-proof image certificate aliases; ambiguous candidates retain obligations. Customer: docs/showcase/finite_set_client.hthr. Validation is in progress.
- 2026-09-05: The finite-set client now proves nested image compatibility with rel_cong alone. A bounded one-argument local dictionary field search supplies a uniquely matching, kernel-checked family certificate; ambiguous candidates retain the compatibility obligation and an explicit alias selects evidence. Focused controls and the full plain Furnace suite pass (2,411 passed, 0 failed, 5 ignored). Broader transfer/search remains open.
- 2026-09-05: The independent tree backend supplies a concrete author-automation customer: connective rearrangement for union laws and branching induction for image membership witnesses. See lib/std/data/set/tree_finite_set.hthr and docs/showcase/setoid-second-backend-round.md; existing checked client automation is reused unchanged.
- 2026-09-05: Started [[named-function-compatibility-derivation]]: explicit named theorem requests, transparent compositional derivation, reusable certificates, and a branch-choice obligation through a checked Boolean choice combinator. List/tree clients and refusal/repair controls are under validation.
- 2026-09-05: Completed [[named-function-compatibility-derivation]] for the bounded homogeneous fragment. The author names an operation and requests a checked preservation theorem; both list and tree clients reuse it. Choice compatibility exposes an explicit stability obligation. Full plain Furnace suite: 2,418 passed, 0 failed, 5 ignored. Arbitrary match/recursion and general parametricity remain open.
- 2026-09-05: Paused implementation expansion at user direction; [[setoid-roadmap-and-resumption]] records the verified baseline, existing owners, and focused follow-ups. Resume from an actual client need rather than treating the backlog as a sequential implementation plan.
- 2026-11-05: gardener: cites a file it shares with [[per-instantiation-projection-boundaries]] (`docs/showcase/finite_set_client.hthr`).
