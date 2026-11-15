---
title: Add concise general tactic-composition syntax
status: open
labels: [surface,proofs,elaboration,syntax]
area: tactics
created: 2026-08-27
updated: 2026-10-31
---

Make common proof-tree composition concise without adding solver-specific
magic. `split_all` should continue to produce ordinary goals and `all_goals`
should continue to apply one block independently to every current leaf. The
follow-up is surface syntax and small general combinators for repetition,
sequencing, and applying a tactic to all goals.

Do not make Omega composable through a special return type or fuse branching
into arithmetic automation. The same syntax must serve `refl`, `omega`, user
metaprograms, and future tactics uniformly.

## Acceptance

- Provide a concise spelling for the common `split_all; all_goals { omega }`
  shape without changing its goal semantics.
- Define failure and empty-goal behavior for sequencing, repetition, and
  all-goal application.
- Preserve the existing explicit block form and nested-goal tests.
- Keep tactic composition independent of any particular solver.

## What it assumes from elsewhere

- `docs/tactics/goal-combinators.md` defines the current `split_all` and `all_goals`
  behavior that new syntax must preserve.

## Log

- 2026-10-01: 2026-10-01: a customer from [[automatic-author-surface]]. wc.hthr's newline_is_space and wc_next_lines split cleanly with split_all, but some leaves close by refl and others by a contradiction among the comparison facts (bv_omega). One leaf body can't do both, so they stay hand-written. Wanted: an alternation leaf (try refl, else bv_omega) with defined failure behaviour.
- 2026-10-31: `tac-in-heather` is marked done in docs/roadmap.md (a Heather `split_all` closes the Rust one's goals), so this issue no longer serves it; it stays open in area `tactics` with no milestone.
- 2026-10-31: 2026-10-31: [[proof-scripts-as-tac-blocks]] proposes absorbing this: once proof scripts are Tac blocks, the concise forms become library combinators rather than grammar.
- 2026-11-05: gardener: cites a file it shares with [[split-all-revise-hypotheses]] (`docs/tactics/goal-combinators.md`); [[split-all-through-recursive-definitions]] (`docs/tactics/goal-combinators.md`).
