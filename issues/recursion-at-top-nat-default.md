---
title: Make recursion at the top the lowering for every Nat recursion
status: open
labels: [recursion,elaboration]
area: language
created: 2026-11-04
updated: 2026-11-04
---

Slice 2 of docs/recursion-at-the-top-design.md §4 option A (Minus chose A,
2026-11-04). Today recursion at the top runs only where the plain lowering
refuses or would not mean its source ([[recursion-below-nat-fallback]],
§5). Make it the lowering for **every** structural recursion on an explicit
`Nat` parameter, then delete the Nat guard selection it makes unnecessary:
`guard_param`'s and `outer_case_split`'s Nat cases, the planner's Nat
`ByMeasure`/`Misplaced` routing, and the retry-on-refusal.

Every Nat recursion's term changes (one more match at the top, the
generalized motive, the static arm choice), so this is a measured round:
`scripts/perf ab` over the library corpus before it lands, counters first.
Choosing the decreasing parameter becomes a search over the explicit Nat
parameters (the planner's guess first).

## Acceptance

- Every library module checks with `--expectations`, with
  `recursion-meaning` (`--review`) clean or no worse than master.
- `perf ab`: no counter regression the report cannot explain; seconds
  inside the spread.
- The Nat guard-selection code is deleted, with its probes
  (`recursion_case_split_tests.hthr`) still passing or converted to
  acceptances with their meanings pinned by `refl`.

## Log

- 2026-11-04: first attempt (patch kept at
  `/mnt/project-files/recursion/nat-default-flip.patch`): every
  non-measure `fn` whose outermost `match` on a parameter has a self-call
  descending through it, that parameter an explicit `Nat`, lowered at the
  top first. The library does not survive it, for two reasons that are not
  bugs in the lowering:
  - **The kernel's fold acceleration is lost.** `eval/runs.rs` and
    `probe.rs` classify a `Nat` eliminator's step as affine or synchronous
    and fold a run of successors at once; `Nat::add`, `Nat::mul` and their
    kin are such folds. At the top the step is a Σ over a Π-generalized
    motive and classifies as opaque, so `1000000 + 1000000 = 2000000` by
    `refl` runs out of fuel (it checks with `add`/`mul` left plain). In the
    library: 190 errors, almost all `OutOfFuel` in the float, int and creal
    tests, `bitvec_signed`, `native_arena`, and one test module's run
    killed at the memory rail.
  - **Which arguments a function computes on changes.** Taking the
    parameter the inner recursion is on moves its `match` outside a case
    split: `inner(d, n)` (recursion_case_split_tests) no longer reduces at
    `d = 0` with `n` open, and `List::drop(Nil, n)` would not either had a
    List-first function been taken.
  Found on the way, and fixed separately: the ih received the varied
  arguments reversed when the decreasing parameter came third
  ([[recursion-varied-arguments-reversed]]); with every other parameter
  generalized at the top it broke `nat.hthr`'s `ldiv_fuel` unfoldings.
  Blocked on a decision: teach the fold classifier the top's shape, flip only
  where the plain step is not a classified fold, or keep the top as the
  fallback.
