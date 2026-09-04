---
title: Validate relational abstraction through an ideal finite-set client
status: open
labels: [stdlib,setoids,transfer,ergonomics,design]
created: 2026-09-04
updated: 2026-09-04
---

Design from client code before committing to lifting syntax or whole-interface
machinery. The exploratory artifact is `docs/showcase/finite-sets-idealized.hthr`;
`docs/finite-set-client-design.md` explains the certificates and open decisions.
The artifact intentionally does not check and is not a language commitment.

## Acceptance

- Build the manual counterpart: membership modulo an element equivalence,
  extensional list/set relation, union, image, and their compatibility laws.
- Check `extend(f,xs) = xs ∪ image(f,xs)`, its compatibility, union law, and
  duplicate-insensitivity theorem. Keep compatibility of arbitrary f explicit
  in the elaborated contract while minimizing client-facing proof plumbing.
- Transport an element-with-membership between equivalent sets and prove the
  result comparison ignoring membership evidence. Retain one witness-sensitive
  negative control. This is the early dependent customer.
- Record a gap table against the idealized file. Do not grow a module/sealing
  system merely to make its proposed `within` block parse: explicit abstract
  carriers, operation dictionaries and parameters are the first fallback.
- Next slice: compare raw folds and duplicate-free folds, showing exactly which
  certificates permit each. Distinguish failure to lift raw length/head/sum
  from the availability of a different cardinality/selection/sum implementation.
- Compare raw and duplicate-free list implementations through operation
  correspondence. Keep decidability local to operations that need it.
- Assess productive diagnostics on a missing image certificate, a conditional
  fold opportunity, and a refuted raw-list observation. These are shared
  tooling customers, not a separate diagnostic framework.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns heterogeneous relational rules.
- **[[setoid-core-api]]** owns the manual setoid foundation.
- **[[relation-indexed-algebra]]** owns relational algebra and dictionary policy.
- **[[setoid-morphisms-and-transport]]** owns interface/implementation transport.
- **[[setoid-auto-lifting]]** owns compositional generation and rewriting.
- **[[dependent-relational-transport]]** owns fiber transport structure.
- **[[subtype-transfer-and-evidence]]** owns evidence-policy comparison.
- **[[ai-facing-tooling]]** owns structured opportunity/failure reporting.

## Three small user experiences

`docs/three-small-transfer-experiences.md` narrows the first teaching/design
surface to `add_neighbors`, positive-natural `twice`, and rejected/repaired
cardinality. Prefer this entry point when assessing natural client syntax;
the earlier idealized file remains the broader interface exploration.

The set examples use a nominal semantic interface instead of a `within` block.
Tentative automatic certificate generation is scoped to declarations using an
explicitly registered semantic interface; raw arrow typing does not establish
compatibility, and consumers still require the checked certificate.

The cardinality repair returns a duplicate-free enumeration view compared by
permutation. Do not accidentally require identity of the intermediate lists:
length is invariant while order may vary. The first negative example is at
Nat so its counterexample and the equality decider for repair are concrete.

Acceptance includes ordinary successful feedback, an expandable guarantee,
exact residual goals, and checked counterexample feedback. Syntax and automatic
entry points remain candidates until compared with manual expansions.

## Log

- 2026-09-04: Wrote idealized client and worked backward to explicit certificates.
  Findings: list parametricity alone does not select finite-set semantics; raw
  fold duplicate-insensitivity and deduplicated folding are distinct capabilities;
  dependent membership transport succeeds modulo an evidence-ignoring relation;
  semantic dictionary equivalence must not silently replace exact parent views.
  No implementation or syntax freeze in this round.
- 2026-09-04: Designed three tiny user experiences; simplified the client surface and made the permutation-valued cardinality repair explicit.
