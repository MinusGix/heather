---
title: bind congruence up to eutt
status: closed
labels: [codata,coinduction,itree,library]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-11-01
---

`Eutt` (`lib/std/itree/coitree_eutt.hthr`) has the monad laws through `of_bisim`,
but not the congruence: `t ≈ u` and `h1(a) ≈ h2(a)` for every `a` give
`bind(t, h1) ≈ bind(u, h2)`. A handler proof up to taus wants it next.

## Shape

Corecursive on `t ≈ u`, as `CoTree::bind_cong` is on `Bisim`:

- a silent step or a call carries over once `after` is known through `bind`:
  `after(k, t) = OTau(t2)` gives `after(k, bind(t, h)) = OTau(bind(t2, h))`,
  and the same for `OVis`, by induction on `k` with `obs_bind_at`;
- at a leaf `r`, `bind(t, h1) ≈ h1(r)` (by `after(k, t) = ORet(r)` and
  `tau_l`), then `h1(r) ≈ h2(r) ≈ bind(u, h2)` by `trans`. That node is an
  existing tree, not a constructor, which the corecursive surface accepts as
  a whole result.

## What it assumes from elsewhere
- **[[coitree-eutt]]** owns `Eutt`, `after` and `trans`. Assumed here: only
  their statements.

## Log
- 2026-11-01: Done (`lib/std/itree/coitree_eutt.hthr`, `docs/itrees/coitree-design.md` §7.5). `Eutt::bind_cong` plus `bind_cong_l`/`bind_cong_r`. A tau or a call carries over at the same counts (`CoTree::after_bind`, guarded by `Obs::NotRet`: a leaf reached before `k` drops would spill the rest into `h(r)`). At a leaf the counts are only upper bounds, so that branch is the existing relation `bind(t, h1) ≈ h1(r) ≈ h2(r) ≈ bind(u, h2)` through `trans` and `Eutt::bind_leaf`. Probes in `lib/_tests/std/itree/coitree_eutt_tests.hthr`. The eutt-level unfolding `f(x) ≈ bind(body(x), f)` of `docs/language/partial-functions-design.md` §4.3 can use it now.
