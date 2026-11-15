---
title: Check positive-natural addition and transferred semigroup laws
status: closed
labels: [stdlib,subtypes,relations,testing]
created: 2026-09-05
updated: 2026-09-05
---

Build the first explicit customer of [[subtype-transfer-and-evidence]]: an ordinary PositiveNat record with .value and relevant positivity evidence, addition from a closure lemma, computation and transferred associativity proofs, and a relation-indexed semigroup instance. Check a generic relational client, a resumable missing-closure goal, incorrect closure evidence, impossible zero construction, and refusal to identify stored proofs. Keep automatic wrapper insertion, general transfer generation, and evidence-policy comparison with the parent issue.

## Log

- 2026-09-05: The CLI probe exposed raw generated record projections in the missing-closure goal. This round also teaches the diagnostic speller to recognize registered single-receiver record projections by nominal identity, without reduction; nested projections and binder context get regressions. General operator resugaring remains owned by [[diagnostic-operator-resugaring]].
- 2026-09-05: Registered dependent-record projections now render in closure goals. [[inline-record-projection-display]] owns the separately discovered inline/nondependent and parameterized-record display gap. This round does not broaden generated-definition registration merely to obtain a spelling.


## Artifacts and boundary

- `docs/showcase/positive_subtype.hthr`: explicit record, closure lemma,
  computation rules, transferred associativity, semigroup instance, concrete
  notation, and an ordinary `twice` client.
- `docs/showcase/positive-subtype-round.md`: user explanation and proof-goal workflow.
- `lib/std/algebra/algebra_rel.hthr`: relation-indexed Semigroup composition, also
  reused as Mergeable's parent.
- The projection diagnostic fix recognizes registered, single-receiver
  record accessors without reduction. [[inline-record-projection-display]]
  owns the remaining inline and parameterized cases.

[[subtype-transfer-and-evidence]] retains automatic construction and law
transfer, the heterogeneous transfer interface, evidence-policy comparisons,
witness-dependent operations/types, and cost measurement. This explicit
customer establishes the first reference behavior for that work.
- 2026-09-05: Completed the explicit PositiveNat wrapper, closure and computation proofs, transferred semigroup laws, concrete notation, twice client, and generic rel_cong client. Missing closure goals resume with on; incorrect evidence, zero construction, implicit raw-result construction, and whole-record refl from unrelated stored proofs are refused. Registered projection diagnostics show Lt(0, add(x.value, y.value)). Focused suite: 51 passed. Independent Furnace CLI showcase and diagnostic probes passed. Final plain furnace run -- scripts/test: 2,362 passed, 0 failed, 5 ignored (294 seconds).
