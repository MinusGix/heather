---
title: Pause setoid expansion until a concrete client drives the next slice
status: open
labels: [setoids,planning,backlog]
area: mathematics
created: 2026-09-05
updated: 2026-10-13
---

## Decision

Pause implementation expansion in this area. The checked examples establish a useful direction; the remaining depth is not, by itself, a reason to keep extending the machinery. These issues preserve options while work moves to other Heather needs. They are not a ranked implementation queue or prerequisites for general language progress.

Keep issues open to record unfinished work. This pause is a prioritization decision, not a technical dependency block. Do not reopen the completed narrow implementation issues merely because the broader area remains unfinished.

## Where we stopped

- Relation-indexed laws, local notation, relational calc, and scoped dictionary projection.
- An abstract finite-set client with independent list and branching-tree backends, plus semantic conversions and selected-element transport.
- Explicit named-function compatibility requests with certificate reuse and resumable obligations; branch support currently uses a checked choice combinator.
- Computation can take operations while theorems take laws. Large dependent dictionary conversion remains a tracked cost limitation.

Baseline commits: `74acfbd`, `e772feb`, `801b84c`. Latest verified implementation: 2,418 tests passed, 0 failed, 5 ignored, plus both derivation CLI showcases. Entry documents: `docs/setoid-author-client-round.md`, `docs/setoid-second-backend-round.md`, `docs/derive-set-functions-round.md`.

## Focused follow-ups captured at the pause

- [[relational-ordinary-branches]] — Derive compatibility through ordinary Boolean branches.
- [[relational-cross-branch-proofs]] — Prove compatibility when related inputs choose different branches.
- [[relational-derivation-diagnostics]] — Explain relational derivation failures at the responsible expression.
- [[relational-certificate-registration]] — Register and discover compatibility certificates explicitly.
- [[relational-recursive-derivation]] — Derive recursive compatibility from constructor cases and induction evidence.
- [[relational-higher-order-derivation]] — Generate proofs through heterogeneous and higher-order relational contexts.
- [[relational-derivation-cost]] — Measure and bound relational search and generated proof cost.
- [[setoid-capability-requirements]] — Keep computation and theorem requirements minimal in relational interfaces.
- [[finite-set-element-relations]] — Compose finite-set semantics with an equivalence on elements.
- [[finite-set-enumeration-and-folds]] — Specify finite enumeration and lawful finite-set observations.
- [[relational-algebra-normalization]] — Normalize relational algebra expressions with checked law certificates.

## Existing owners retained

| Area | Existing issue |
| --- | --- |
| Overall generation and explicit lifting | [[setoid-auto-lifting]] |
| Morphisms, function-valued representations, rationals | [[setoid-core-api]] |
| Manual operation, theorem, and structure transfer | [[setoid-morphisms-and-transport]] |
| Heterogeneous relators and quantifier transfer | [[relational-transfer-core]] |
| Universally quantified per-function parametricity | [[certified-parametricity]] |
| Varying fibers and dependent rewriting | [[dependent-relational-transport]] |
| Subtype closure, witness relevance, and lifting | [[subtype-transfer-and-evidence]] |
| Algebraic theory migration and exact dictionary views | [[relation-indexed-algebra]] |
| Rewrite direction, occurrences, and relation explanations | [[relational-rewrite-controls]] |
| Named index introduction and notation | [[constraint-index-binder-introduction]] |
| Dependent dictionary conversion cost | [[setoid-dictionary-projection-growth]] |
| Finite-set client experiments | [[finite-set-client-design]] |
| Optional checked counterexamples | [[heather-disprove]] |

The boxed-code/metaprogram implementation remains under [[setoid-auto-lifting]], coordinated with [[in-language-certificate-emission]]. The native request is not completion of that architecture; no duplicate migration issue is needed here.

## What should bring us back?

Resume when a real subsystem needs to compare representations or transport an operation/theorem, and its current proof or implementation cost is visible. Possible sources include a compiler transformation, a mathematical representation already needed elsewhere, or an actual collection consumer. Do not build one just to justify this backlog.

At resumption, record the concrete operation/client, chosen relations, observations that must remain valid, current manual proof, and an acceptance measure such as removed proof plumbing or bounded checking cost. Select the smallest coherent subset of this map that helps that client. A successful finite-set showcase does not establish a need for every listed extension.

## Log

- 2026-10-10: Resumed at user direction with rationals as the client (docs/setoid-rationals-round.md). Recorded per "At resumption": the client is unreduced `Rat` (lib/std/rat.hthr) over `Pos` (lib/std/pos.hthr); the relation is cross-multiplication `≈`; the observations that must stay valid are + * - inv ≤ and the `ofInt` embedding, with the denominator proved not to be one; the acceptance measure is a client (docs/showcase/rat_client.hthr) that rewrites with `calc` over `≈` and `rel_cong` and never opens a fraction. The existing setoid tooling needed no change. The cost went to ring rearrangement ([[ring-normalization]]) and omega restatements ([[omega-unfolds-defined-propositions]]). The next native-side client is [[same-defined-state-setoid]], after [[native-straight-code-triples]].
- 2026-10-13: The native client, [[same-defined-state-setoid]], is done. `SameDefinedState` became `=` pulled back along `erase_af`, with an `Equivalence` instance, `≈` designated at `MachineState`, and `evidence theorem` certificates that `rel_cong` finds. The existing tooling needed no change. The cost it surfaced is [[setoid-surface-kernel-cost]].
