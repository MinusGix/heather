---
title: Rebuild while and for on the one loop combinator, and the native loops on one node
status: open
labels: [loops, elaborator, native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-19
updated: 2026-11-19
---

Design: `docs/language/loop-combinator-design.md`. Round 1 (the combinator
`lib/std/core/loop.hthr`, `Loop::rule`, `Loop::unique`, `induct` on a
non-recursive step, `let`-bound facts released for searches, probes) is
built. Left, each a PR for Minus (§8 of the design):

2. `while` and counted `for` elaborate to `Loop(…).run(…)` with the facts in
   the state; the lifted-loop family (`f#run`, `T::f_loop`, `#ext`,
   `#irrel`, `#induct`, `#keepsK`, `#found_N`) goes; the library's proofs
   that cite it move to `Loop::rule`.
3. One loop node in the shared term language, agreement as a relation kept
   by a pass, proved once over `Function::run`; tail mode and
   `Fun::Guarded` go.
4. `rt_file_loop`, `rt_held_loop`, `rt_bytes_loop` and `rt_io_loop` onto it.
5. The port ledger's loop rows.

## What it assumes from elsewhere
- **[[span-caller-of-fact-taking-loop]]** owns the refused caller of a loop
  with facts. Assumed here: only that passing the facts in the initial
  state retires it once round 3 lands.

## Log
- 2026-11-19: round 1 built; the binary search's theorem re-proved by
  `Loop::rule` at about the example's length (the cost check the design
  asked for).
