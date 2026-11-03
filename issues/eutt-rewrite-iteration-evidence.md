---
title: Respect evidence for Eutt iteration and the world reading
status: open
labels: [setoids,relations,coinduction,itree]
area: tactics
milestone: [nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

`rewrite` along `Eutt` (`docs/equation-rewrite-design.md` §11) has evidence
rules for `bind`, `map`, `CTau` and `CVis` (`coitree_eutt.hthr`). The loop
and reading combinators get theirs from [[eutt-iteration-and-io-reading]]'s
congruences once they land: `CoTree::iter` over its body pointwise
(`Eutt::iter_cong`), `CoTree::rec`/`mrec`, and `Io::against_co`, which maps an
`Eutt` tree to an `Eutt` reading at another carrier and so is a §11.4 rule
(`PreservesRelation(Eutt::Rel<…>(E), Eutt::Rel<…>(…), λ t => Io::against_co(t, io))`).
Each is a one-line `evidence theorem` over the congruence, plus a probe that
rewrites under it.

## Log

- 2026-11-03: 2026-11-03: Landed with [[eutt-iteration-and-io-reading]] (PR #409): `Eutt::iter_respects` (`coitree_eutt.hthr`) and `Io::against_co_respects` (`linux_world_co.hthr`, the §11.4 case) with probes that rewrite under them (`rewrite_in_loop`, `rewrite_in_reading`). `Eutt::mrec_respects` is stated (`coitree_rec.hthr`) but `rewrite` does not find it for a run over `Events::sum(calls(Nat, Nat), none)` ("no evidence about it names the relation its result changes by"); the probe `rewrite_in_run` records that refusal. Left here: why the lookup misses it (likely unifying `Events::sum(D, E)` against the reduced event record), and `CoTree::rec` over a dependent body, which `Pointwise` cannot state.
