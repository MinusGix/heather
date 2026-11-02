---
title: One unfold-to-head primitive for the seventeen bounded reduct walks
status: open
labels: [elaboration,refactor]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Seventeen call sites walk "up to N reducts of a term, take the first whose
head satisfies P" through `SemanticOracle::term_reducts`, with budgets 1, 4,
8, 8, 16, 16, 16, 32, 32, 64 (×5) and 1024 (×2): omega_cert.rs (×3),
resolve.rs (`UNFOLD_STEPS`), ring.rs (`WRAPPER_STEPS`), host.rs
(`HOLE_UNFOLD_STEPS`), goal_combinators.rs (×4), lib.rs (×2, one is
`INDEX_UNFOLD_STEPS` from #387), bv_omega.rs, relational_context/proof.rs
(×2), literals.rs, iwf_family.rs, indexed.rs. Each budget was tuned to its
first customer, and a step count mixes a δ step on a large definition with a
β step (docs/elaborator-principles-survey.md §5).

## Proposal

1. Refactor: one primitive `unfold_to(term, transparency, pred)` in
   `oracle.rs`, every site calling it with its predicate and **its current
   budget**. No behaviour change: `scripts/timings --diff` shows identical
   count columns.
2. Then, with [[unifier-lazy-delta]]'s δ-lazy order (and definitional
   heights if adopted), sites drop their budgets one at a time, keeping one
   shared fuel policy for genuine computation. Interface definitions stay
   opaque through the transparency parameter.

Out of scope: display budgets, `STUCK_SPELLING_STEPS`, kernel fuel.

## Acceptance

Step 1 lands with identical counters over the library; each site removed
from the budget list in step 2 cites the probe that shows it unchanged.
