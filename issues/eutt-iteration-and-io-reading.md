---
title: Loops up to taus, and the world reading as a coinductive Io::Reads
status: closed
labels: [coinduction,itree,effects]
area: interaction-trees
milestone: [nh-effects]
created: 2026-11-03
updated: 2026-11-03
---

The library half of `docs/language/effects-capabilities-design.md` §4 (decided by
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

- 2026-11-03: 2026-11-03: DONE, every lemma proved by direct corecursion; nothing waits on [[codata-up-to-friends-round-2]]. `docs/itrees/coitree-design.md` §7.9 has the shape of each proof.
  - `coitree.hthr`: `iter_from` (the loop resumed inside a pass), `Obs::iter`, `iter_next`, `iter_at`, and the unfolding `CoTree::iter_unfold` as a `Bisim` (`iter(body, a)` is `bind(body(a), Continue(a2) ↦ CTau(iter(a2)) | Break(b) ↦ CRet(b))` step for step).
  - `coitree_eutt.hthr`: `AfterIs` and `CoTree::after_map` (any function of trees that is a function of observations and keeps silent steps follows the drops with an exact count; `iter_from`, `mrec`, `against_co` are instances by `refl`), `Eutt::iter_from_cong`/`iter_cong`, `Eutt::iter_unfold` (tau dropped, `iter_again`).
  - `coitree_rec.hthr`: `Returns::eutt`, `Eutt::mrec_cong`/`rec_cong` (via the `MrecStep` classification of a command), `Eutt::mrec_call`, and `Eutt::mrec_bind` (running a bind is running its halves in sequence) generalised over `Bisim(p, bind(q, k))` so `bind_assoc` lands in the hypothesis.
  - `linux_world_co.hthr` (new, so the modules that only run programs against a world do not load the coinductive library): `Io::against_co` (each `CVis` answered by the world as one `CTau`), `against_co_cong`, `against_co_bind` (a `Bisim`), `Io::Reads` restated as `Eutt` at every world (the finite `Reads`/`reads_*` removed; nothing else used them), `reads_ret`, `reads_trigger`, `reads_bind`, the loop lemma `Io::reads_iter` into `Io::iterate` (`CoTree::iter` in `Partial` over `Mutated<Io, A>`), and the bridge `Io::against_returns` (a fuelled `against(t, io) = Some(m)` gives `Returns(against_co(of_tree(t), io), m)`).
  - The loop lemma's plain statement needs up to `trans`; `Io::reads_loop` generalises the hypothesis to "the pass's reading ≈ the iteration's pending pass" and traces the reading's taus and returns back to the pass (`pass_tau`, `pass_ret`, induction on the count). Written up as a rule in `docs/proof-patterns.md` §4.
  - Probes: `linux_world_tests.hthr` reads a fuel-free `cat_co` at the piped world to `Returns` at count 7 by `refl` (status, bytes, and the whole `Mutated` against `Io::cat`), a failing write at count 2, too-short and wrong-value controls, a fuelled probe carried over by `against_returns`, and `yes` (never ends) through `reads_iter` at a neutral world; `coitree_eutt_tests`/`coitree_rec_tests` use `iter_cong`, both unfoldings, `rec_cong` with `Returns::eutt`, and `mrec_bind` at open arguments.
  - Found on the way: `inj` through a corecursive function's observation is accepted by the elaborator and refused by the kernel (`NotInferable`): [[kernel-refuses-inj-through-corecursive-reduct]] (closed 2026-11-04; `pass_ret` uses `inj` again).
