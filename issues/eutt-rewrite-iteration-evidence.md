---
title: Respect evidence for Eutt iteration and the world reading
status: blocked
labels: [setoids,relations,coinduction,itree]
area: tactics
milestone: [nh-effects]
blocked-by: [eutt-iteration-and-io-reading]
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
