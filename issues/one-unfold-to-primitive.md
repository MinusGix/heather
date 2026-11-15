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
β step (docs/elaborator/elaborator-principles-survey.md §5).

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

## Log

- 2026-11-03: Step 1 built. `SemanticOracle::unfold(gamma, term, walk)`
  is the one reduct walk, and `unfold_to(…, read)` is it read for the first
  reduct `read` answers. `term_reducts` and the six per-file budget constants
  (`PROPOSITION_UNFOLD_STEPS`, `UNFOLD_STEPS` ×2, `WRAPPER_STEPS`,
  `HOLE_UNFOLD_STEPS`, `INDEX_UNFOLD_STEPS`) are gone. Every budget is a
  variant of `oracle::Unfold`, named by what its walk looks for, with the
  budget it had: `OneStep` 1, `RingWrapper` 4, `Comparison`/`IndexRead` 8,
  `HoleComparison`/`MatchedArm`/`WordShape` 16,
  `InstanceBit`/`LiteralEmbedding` 32, `Proposition`/`RuleGoal`/
  `StuckScrutinee` 64, `FamilyEncoding` 1024. The 17 sites keep their
  predicates where they were: most are loops whose body returns from the
  enclosing function, and those stay loops over `unfold`. The four
  find-the-first sites (`unfolded_proposition`, `bv_omega`'s word shape, the
  two family encodings) use `unfold_to`. No transparency parameter yet: every
  walk is transparent today, and an interface definition is withheld on the
  kernel Ψ the walk reads, so the parameter waits for a walk that needs
  another setting. Step 2 retires the variants one at a time.

