---
title: Keep the num and analysis modules well inside the gate's per-module CPU rail from a cold store
status: closed
labels: [testing, performance, elaborator]
area: infrastructure
created: 2026-11-01
updated: 2026-11-01
---

Four PRs saw the library gate's `lib/_tests/std/num` folder killed at the
300 s CPU rail on a cold rebuild, and #346 saw `lib/std/analysis` killed the
same way. Every rerun passed.

## Why it was killed

The gate's build step (`crates/cli/tests/library.rs`) checks each module
in a `heather check` of its own, so each module has its own 300 s rail
(`docs/module-dag-design.md` §12). A folder's check then only replays, so it
is cheap (`lib/_tests/std/num` replays in about 15 s once its closure is
built). But if one module of the closure is killed in the build step, every
module after it is left unbuilt. The folder check then elaborates all of
them in one process and hits the rail too. That is the failure the four PRs
reported. It names the folder, not the module that started it.

Measured cold from the master sentinel's seed (`f9c6e9d`'s stores) on a
4-CPU cloud box, master `a24a2b3`, kernel width one, four build jobs. The
three largest modules were near the rail by themselves:

| module | build step (s) |
|---|---|
| `real_fn` (`lib/std/analysis`) | 202 |
| `trig_law` (`lib/std/num/float`) | 155 |
| `native_compile_correct` | 148 |
| `real_log` (`lib/std/analysis`) | 128 |
| `eft` | 99 |

A ±30–40% swing on a cloud box takes any of them past 300 s. `real_fn` is
imported by `real_exp`, `real_log` and the num folder's `trig_real_tests`
closure, so a kill there reaches the analysis folder and the num test folder.

Six declarations were most of the cost: `DerivOn::chain`, `DerivOn::mul`,
`DerivOn::mul_step` and `DerivOn::mvi_steps` in `real_fn`,
`CReal::cos_add_near` in `trig_law`, and `Series::atanh_ratio_step` in
`real_log`. There were two causes.

1. **The elaborator rebuilt the goal world on every goal query.**
   `GoalArena::world` (`crates/elab/src/goals.rs`) extends Ψ with one binding
   per slot. A transparent slot's binding is its context, type and body,
   shifted past the slots before it. It was rebuilt on every
   `goal_psi`/`goal_oracle` call, which `resolve_goal`'s `conv_here` makes for
   each `linarith` hypothesis. A long `let` chain of `linarith` steps has many
   transparent slots, so it paid every slot's shift on each query.
   `cos_add_near` spent most of its 68 s there (gdb stack samples), and the
   kernel gate's time column counted it, because `conv_here` is timed as
   kernel time.
2. **Nested witnesses taken from theorem results.** `DerivOn::chain` and
   `DerivOn::mul` set `let au = below_both(a0.witness, ..)` and `let ad =
   below_both(au.witness, ..)`, and then build their result over
   `ad.witness`. The kernel check of that body normalised the nested
   witnesses together with the proofs behind them: 8.3M and 8.9M steps. This
   is [[match-on-proof-call-cost]]'s mechanism, reached through projections.

## What changed

- `GoalArena` keeps each slot's binding once it has a goal
  (`slot_bindings`). A goal never changes after it is pushed, and the arena
  only appends, truncates and clears, so the cache grows and shrinks with
  the goals. The world is the same, and every counter in `--timings` is
  identical before and after: steps, queries, misses and gated declarations.
- `DerivOn::chain` and `DerivOn::mul` compute their moduli with `let` and
  hand them all to `DerivOn::chain_close` and `DerivOn::mul_close`, whose
  parameters they are. The statements are unchanged.
- `docs/proof-patterns.md` §4 has the rule.

## Measurements

The module's own declarations, cold verdicts, kernel width one, three probes
running side by side:

| module | before (s) | after (s) |
|---|---|---|
| `trig_law` | 146 | 82 (goal world) |
| `real_log` | 114 | 63 (goal world) |
| `real_fn` | 201 | 172 (goal world), then 101 (`*_close`) |

| declaration | before | after |
|---|---|---|
| `CReal::cos_add_near` | 73 s | 27 s |
| `Series::atanh_ratio_step` | 66 s | 12 s |
| `DerivOn::mul_step` | 24 s | 8 s |
| `DerivOn::chain` | 45 s, 8.3M steps | 5.4 s + 1.9 s, 0.92M steps |
| `DerivOn::mul` | 40 s, 8.9M steps | 6.7 s + 4.7 s, 1.07M steps |

The whole cold build step from the same seed, run the same way: 680 → 469 s
wall, and 2025 → 1628 module-seconds. `real_fn` 202 → 110 s and `trig_law`
155 → 93 s. The largest module is now `native_compile_correct`, at 146 s.

## Left

- `real_exp`'s `CReal::exp_sub_lin_near` (19M steps) and `elementary_real`'s
  `CReal::trig_add_at` (11.5M) are the next heavy items in the analysis and
  num chains. Neither has been checked for this shape yet. Both are logged on
  [[match-on-proof-call-cost]] as candidates.
- A measuring pitfall: an `--only` probe over a store that already holds
  the item's verdicts reports kernel and elaborator counts that a cold run
  does not reproduce. `DerivOn::chain` showed 32K steps under `--only` and
  8.3M cold. Strip the declaration verdicts, or use a fresh store, as
  `docs/proof-patterns.md` §7 says.

## Log

- 2026-11-01: Filed and closed in one round (this file).
