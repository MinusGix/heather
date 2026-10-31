---
title: One dependent-match compiler: motive by abstraction, the equation always in scope, clause equations
status: open
labels: [design,elaboration,match,proofs]
area: language
created: 2026-10-31
updated: 2026-10-31
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
