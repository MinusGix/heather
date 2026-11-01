---
title: One dependent-match compiler: motive by abstraction, the equation always in scope, clause equations
status: open
labels: [design,elaboration,match,proofs]
area: language
created: 2026-10-31
updated: 2026-11-01
---

Item 2 of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s): every `match` generalizes its scrutinee, refines whatever
mentions it, and gives each arm the equation `scrutinee = Ctor(…)`, without
being asked. 26 open issue titles are about `match` or motives (2026-10-31).

## Symptoms this would retire

- Hand convoys: `lib/std/text/decimal.hthr`'s `leb_no` is
  `(match a.leb(b) as λ found => (a.leb(b) = found) → found = False { … })(refl)`.
- [[unfolding-computed-scrutinee]]: `decreases` over a computed scrutinee
  gets no equation, which is why the decimal formatter uses fuel and why
  `while … decreases` (R3b) waits.
- `let x = match c { … }` in inference position is refused for lack of a
  motive (the sequencing design's probe P2).
- [[match-motive-surface-audit]], [[uncurried-recursions-library-sweep]], and
  the course-of-values convoy issues.

## Scope (design first)

1. A motive by abstracting the scrutinee out of the expected type and out of
   every local whose type mentions it. `as λ` becomes an override.
2. An equation in every arm, named with `match h:` or anonymous but visible to
   `omega`, `split_all` and `rewrite`.
3. Non-dependent matches infer their type in inference position.
4. Nested patterns compile to case trees with per-clause equations, so the
   `decreases` unfolding walk needs no special cases.

Measure the whole library before replacing the current path: convoys
enlarge terms.

## Done when

A design note decided by Minus, with its slices filed, naming which open
issues each slice closes.

## Slices (docs/dependent-match-compiler-design.md §11)

1. [[match-equation-in-every-arm]]
2. [[match-refines-computed-scrutinee]]
3. [[match-infers-constant-motive]]
4. [[unfolding-through-convoyed-match]]
5. [[match-clause-equations]] (owns [[eqbind-deep-pattern-kernel-rejects]])
6. [[match-equation-indexed-family]]
7. [[match-motive-sweep]]

## Log

- 2026-10-31: Design note docs/dependent-match-compiler-design.md, awaiting Minus's decision (§13). Census of 1443 written motives: 601 hand-carried hypotheses, 339 non-dependent, 259 equation convoys, 244 dependent goals. A `--review` sample finds 180 of 379 already redundant. Six probes on master (§2.1), one of them a new elaborator-accepts/kernel-rejects defect. Seven slices filed.
- 2026-10-31: Decided: equation only when read, anonymous equation unspellable, order 4 (landed) → 1, 3, 2, 5, 6, 7 (design §13).
- 2026-10-31: Slice 1 (match-equation-in-every-arm) done on PR #318: the anonymous arm equation, in the term only when an arm needs it (§4.3.1).
- 2026-10-31: Slice 3 (match-infers-constant-motive) done on PR #318 (§6.1).
- 2026-10-31: Slice 2 (match-refines-computed-scrutinee) done on PR #318 (§5.1).
- 2026-10-31: Slice 6 (match-equation-indexed-family) done on PR #318 (§9.1). Slice 5 blocked on the W child spelling (match-clause-equations' log).
- 2026-11-01: Slice 5 landed (design §7.1): the motive's child rewrap for Wf and W plain children; match-clause-equations, eqbind-deep-pattern-kernel-rejects and nested-match-on-list-tail-motive closed. Follow-ups filed or logged: [[indexed-deep-pattern-kernel-rejects]], [[deep-pattern-dependent-later-field]]. Slice 7 (sweep) remains.
