---
title: Rewrite along Eutt inside eutt goals and under binds
status: open
labels: [setoids,relations,tactics,coinduction]
area: tactics
milestone: [tac-general,nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

Rewriting along `Eutt`: `rewrite(h, e)` with `h : Eutt(t, u)`
([[rewrite-setoid-relations]], `docs/equation-rewrite-design.md` §9) inside
a goal `Eutt(…)`, including under a `bind` continuation's binder
([[rewrite-setoid-under-binders]], closed). Effectful-loop proofs
(`docs/effects-capabilities-design.md` §4, decided by Minus 2026-11-03) are
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
