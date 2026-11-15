---
title: Rewrite along Eutt inside eutt goals and under binds
status: closed
labels: [setoids,relations,tactics,coinduction]
area: tactics
milestone: [tac-general,nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

Rewriting along `Eutt`: `rewrite(h, e)` with `h : Eutt(t, u)`
([[rewrite-setoid-relations]], `docs/tactics/equation-rewrite-design.md` §9) inside
a goal `Eutt(…)`, including under a `bind` continuation's binder
([[rewrite-setoid-under-binders]], closed). Effectful-loop proofs
(`docs/language/effects-capabilities-design.md` §4, decided by Minus 2026-11-03) are
chains of the monad laws and tau laws under binds; today each is a hand
`Eutt::trans` tower.

## Scope

- Register `Eutt<R>(E)` as a relation the rewriter uses: `refl`, `sym`,
  `trans` exist in `coitree_eutt.hthr`.
- Respect evidence for `CoTree::bind` (from `Eutt::bind_cong`), `map`,
  `iter` and `rec` (from [[eutt-iteration-and-io-reading]]).
- `Io::against_co` maps `Eutt` trees to `Eutt` readings at another carrier,
  which is [[rewrite-setoid-heterogeneous]]'s case.

## What it assumes from elsewhere
- **[[rewrite-setoid-heterogeneous]]** owns rewriting through a function
  that leaves the carrier. Assumed here: only that `against_co` waits for it.

## Done when

A probe rewrites `Eutt::bind_assoc` and `Eutt::tau_l` inside an `Eutt` goal,
once at the top and once under a continuation's binder, with no hand
`trans`, and a refusal names the missing respect evidence for a function
that has none.

## Log

- 2026-11-03: done (`docs/tactics/equation-rewrite-design.md` §11). `Eutt` goals
  read as relation applications (an indexed codata family whose last two
  indices are the sides); `Eutt::Rel<R>(E)` names the relation, with an
  `Equivalence` instance (instance indices may now be a global applied to the
  instance's binders); codata constructors match as occurrences, so
  `Eutt::tau_l` and `Eutt::bind_ret_l` instantiate unapplied; respect evidence
  for `bind` (both arguments), `map`, `CTau`, `CVis`. The probes in
  `lib/_tests/std/itree/coitree_eutt_tests.hthr` rewrite `bind_assoc` and
  `tau_l` at the top and under a continuation's binder with no hand `trans`,
  and a function with no evidence leaves a `?compatibility` naming it.
  Through `bind`'s tree at another result type is
  [[rewrite-setoid-heterogeneous]]'s case, done in the same round.
  Not done: walking *into* a constructor ([[rewrite-setoid-codata-constructors]]);
  `iter`/`rec`/`against_co` evidence waits on [[eutt-iteration-and-io-reading]]
  landing its congruences ([[eutt-rewrite-iteration-evidence]]).
