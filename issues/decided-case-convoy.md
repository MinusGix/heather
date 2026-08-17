---
title: Case analysis on a decided predicate: the convoy plus the hoisted branch
status: closed
labels: [frontend,elaboration,proofs,design]
created: 2026-08-05
updated: 2026-08-17
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
- 2026-08-17: ANSWERED by waves L2'/L3 (2026-08-17, [[std-list-l2-prime-laws]], [[std-list-mem-and-perm]]), which branched on a decided predicate seven times across two files — three at logic::or_pick over decide<Le(x, h)>() and four at a raw Bool filter predicate. This issue's own question was whether the forced COMBINATION needs anything beyond [[match-with-equation]] and [[ih-generalization]] landing. Measured: (1) the hoisting half never appeared — insert branches through or_pick and every lemma about it recurses directly, so no branch had to be hoisted into its own fn; (2) the convoy half is one token, `match e : p(h)`, and only ONE of the seven sites even needed the equation (filter_filter, where the goal's second occurrence of p(h) is unreachable from the motive); (3) what all seven pay instead is a third thing this issue did not name — the inner motive has to restate the callee's body, because motive synthesis abstracts only SYNTACTIC occurrences of the scrutinee and does not whnf the goal first. That residue is filed as [[goal-motive-by-scrutinee-abstraction]] and ranked #1 by the round. Closing per README rule 3: scope answered, residue owned.
