---
title: Case analysis on a decided predicate: the convoy plus the hoisted branch
status: open
labels: [frontend,elaboration,proofs,design]
created: 2026-08-05
updated: 2026-08-05
---

Filed as the owner of [[list-algorithms-exercise]]'s ranked still-hurts
item 2 (2026-08-05), whose log has the full text and examples. The shape:
branching on `leb(n, m)` inside a proof takes TWO mechanical devices at
once — the convoy (explicit motive threading the equation) and hoisting
the interesting branch into its own `fn` so the recursive call can be
passed in. Each is understood alone; their forced combination is the tax.

Related but distinct: [[match-with-equation]] owns the equation-arm
binding (would remove the convoy half); [[ih-generalization]] owns the
motive computation (would remove the hoisting half in some cases). This
issue owns deciding whether the combination needs anything beyond those
two landing, and closes trivially if not.

## What it assumes from elsewhere
- **[[list-algorithms-exercise]]** (closing) owns the evidence. Assumed
  here: only the ranked-list entry and its examples.

## Log

- 2026-08-05: [[match-with-equation]] landed (2026-08-05): `match h : e { … }` binds the equation in every arm, so the convoy half of this issue's forced combination is now one token. What remains here is the hoisting half ([[ih-generalization]]'s territory) and the question of whether the combination needs anything beyond both landing.
