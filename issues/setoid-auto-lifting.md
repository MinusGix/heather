---
title: Generate relational compatibility, lifted operations, and transfer proofs
status: open
labels: [kernel,metaprogramming,design]
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

The tiny examples in `docs/three-small-transfer-experiences.md` propose
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

- 2026-07-23: Filed from foundations discussion (see [[kernel-v1-extensions]]
  log of the same date): quotients stay out of the kernel for now, setoids +
  this auto-lifting story are the plan of record.
- 2026-09-04: Expanded from the agreed relational-transfer design; implementation remains open.
- 2026-09-04: Linked the ideal finite-set client and shared proof-opportunity diagnostics.
- 2026-09-04: Recorded the narrow automatic declaration-checking candidate and the intermediate enumeration relation probe.
- 2026-09-04: Added the user-authored interface and relational-calculation probe; normal failure reporting requires no counterexample finder.
- 2026-09-04: **[[manual-mergeable-round]]** supplies a checked `merge_twice` proof with explicit transitivity and compatibility, and a realized showcase. This is the target construction for relational rewriting to reproduce; no generator landed in that round.
- 2026-09-04: The next context-construction slice adds explicit constant and dependent-on-input function application certificates, plus a self-related binary helper, in `std/relation_context`. `docs/showcase/relational-contexts.hthr` exercises nested and repeated occurrences. See `docs/relational-context-round.md`; automatic context discovery and relational calc remain open. The constructors are transparent functions so proof-relevant evidence can compute. Focused validation: 7 passed. Final plain Furnace suite: 2,322 passed, 0 failed, 5 ignored.
- 2026-09-04: Started [[bounded-relational-context-generator]]: explicit source-level context generation, structured missing-evidence goals, and isolated checking. Boxed-code/meta-layer implementation remains open.
- 2026-09-04: Started [[single-contextual-rewrite]]: recover a binder-free context from a theorem goal and named relation proof, then reuse the bounded certificate planner. Native tactic and meta-layer integration remain open.
- 2026-09-04: [[single-contextual-rewrite]] is complete for the bounded source driver: repeated/partial occurrences, checked missing obligations, and ordinary generated proof application. Full suite: 2,336 passed, 0 failed, 5 ignored. Higher-order contexts, calculation chains, native tactic integration, and the boxed-code implementation remain open.
- 2026-09-05: [[proof-position-relational-congruence]] connects supplied lemma applications to ordinary local proof goals. The first native fragment uses resolved terms and one homogeneous relation, class parent resolution, and resumable compatibility goals.
- 2026-09-05: [[proof-position-relational-congruence]] is complete for homogeneous unary/binary contexts at Type<0>. The library now uses supplied lemma applications with local law resolution and ordinary resumable goals. General relation changes, dependent/higher-order contexts, calculation chains, and boxed-code integration remain open. Final plain Furnace suite: 2,348 passed, 0 failed, 5 ignored.
