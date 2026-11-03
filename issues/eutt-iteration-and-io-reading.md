---
title: Loops up to taus, and the world reading as a coinductive Io::Reads
status: open
labels: [coinduction,itree,effects]
area: interaction-trees
milestone: [nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

The library half of `docs/effects-capabilities-design.md` §4 (decided by
Minus 2026-11-03): loops over a world mean `Io → Partial<Mutated<Io, R>>`,
and a tree agrees with a capability program up to taus.

## Scope

In `lib/std/itree/coitree_eutt.hthr` / `coitree_rec.hthr`:

- `Eutt::iter_cong` (bodies pointwise `Eutt` give `Eutt` loops) and the
  one-pass unfolding `iter(body, a) ≈ bind(body(a), Continue(a2) ↦
  CTau(iter(body, a2)) | Break(b) ↦ CRet(b))`; the same for `CoTree::rec`.
- `Returns` respects `Eutt` (`Returns(t, r) → Eutt(t, u) → Returns(u, r)`),
  so specs stated with `Returns` never see `Eutt`.

In `lib/std/os/linux/linux_world.hthr`:

- a corecursive reading `Io::against_co(t: CoTree<R>(Events::linux()), io)
  → Partial<Mutated<Io, R>>` (each `CVis` answered by the world, `CTau`
  kept), with `against_co_cong` (`Eutt` trees read as `Eutt` results);
- `Io::Reads` restated as `Eutt` at every world, with `reads_ret`,
  `reads_trigger`, `reads_bind` and **the loop lemma** `reads_iter` (a
  body that reads as a step gives a loop that reads as the step's iteration
  in the `Partial` carrier), each proved once;
- the bridge to today's fuelled reading: `Io::against(t_n, io) = Some(m)`
  at some fuel gives `Returns(against_co(of_tree …), m)`
  (`coitree_bridge.hthr`), so the existing `refl` probes carry over.

## What it assumes from elsewhere
- **[[codata-up-to-friends-round-2]]** owns coinduction up to `trans` and
  up to `bind`. Assumed here: only that a proof which needs a self-call under
  `trans`/`bind_cong` can wait for it. State every lemma first, prove what
  direct corecursion allows (as `Eutt::bind_cong` was), and log which ones
  wait.

## Done when

The lemmas above are proved or stated and logged as waiting on up-to
coinduction, `reads_iter` among the proved ones if direct corecursion
suffices, and a probe reads a fuel-free loop tree at a scripted world to a
`Returns` with a count by `refl`.

## Log

### 2026-11-03: the friends of `Eutt` are in (from [[codata-up-to-friends-round-2]])

A proof may now call itself under `Eutt::up_to_bisim` and `Eutt::bind_up`
(end of `coitree_eutt.hthr`). `lib/_tests/std/itree/coitree_eutt_tests.hthr`
proves the loop congruence and the one-pass unfolding that way (`iter_cong`,
`iter_unfold`, as probes; promote them into the library here). A friend
must sit under a constructor: state the self-calling lemma for `CTau`-wrapped
trees and peel the taus with `tau_l`/`tau_r`, as `iter_cong_tau` does.
