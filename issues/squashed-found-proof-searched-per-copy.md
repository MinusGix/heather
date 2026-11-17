---
title: A squashed found proof is searched for at every copy of a decreases body
status: open
labels: [performance,elaborator,recursion]
area: language
created: 2026-11-14
updated: 2026-11-17
---

A `decreases` function is lowered to several declarations that each elaborate the body's syntax: `f#body`, `f#ext` and `f_unfold` (`measure::companions`). `f#ext` and `f_unfold` spell the body several times over. A call in the body that leaves a proof to a search (`v.at(j + 14)`, whose `inside` defaults to `bv_omega`) is searched for at every one of those spellings.

`measure::lift_found` exists so that such a proof is found once, as `f#found_N`, and named at each call ([[found-proof-differs-across-recursion-companions]]). Since conditions are taken squashed ([[strict-conditions]], 2026-11-14) the lifting skipped squashed goals, because the equation no longer needs them lifted: squashed proofs convert. The cost came back with the skip.

## Measured

2026-11-14, master 668d983, test-profile binary, self-checks off, width one, `--timings`:

- A recursive function over `[u32; 64]` with one store and one read, both found: 3.5 s. Its body without the recursion: 0.06 s.
- `Sha256::expand` as a plain `fn` (`lib/native/crypto/sha256_schedule.hthr`, five found proofs): 6.5 s, of which `Sha256::expand#ext` 3.5 s and `Sha256::expand_unfold` 2.2 s against 0.3 s for `Sha256::expand#body`.
- With the squashed goals lifted again: `#ext` 0.05 s, `_unfold` 0.035 s, `#body` 0.008 s, and five `#found_N` at 0.01 to 0.05 s each.
- As `runtime fn`s: `Sha256::expand` 11.2 s to 5.1 s, `Sha256::begin` 4.0 s to 2.2 s; the module `sha256_schedule` 19.6 s to 12.1 s and `runtime_held_index_tests` 33.8 s to 17.9 s. `lexer_scan` and `sha256_compression` do not move: their cost is elsewhere.

## Done

`MeasureContext::measure_default_goals` lifts a squashed goal at its squashed type. The probes in `lib/_tests/std/core/squash_conditions_tests.hthr` keep a squashed pair that is not lifted (`block_spread`, defaults written as blocks), so the conversion of squashed proofs is still what one test rests on.

Two more ways the search escaped the lifting (2026-11-17, a lifted `while` with an `invariant`, whose next-state fact is found at the end of the body):

- The query that finds a call's default goals bound each `let` in scope as a local of its type, so a search that reads what a `let` is (`let j₂ = j - 1` before `found_fact<j₂ <= i>()`) failed there and was left at the call. `measure_default_goals` now asks again with the values bound as aliases when the plain telescope fails (`MeasureContext::measure_query_valued`).
- `check_condition_squashed` inferred an argument at a squashed position in a probe, threw it away, and checked it again; an argument `k` deep in squashed positions ran its searches `2^k` times. The inference is kept where it answers squashed at the expected type.

The loop went from 15 s to 2 s.

## Left

- A default the lifting does not know (a block, a tactic other than a context search) is still searched for at every copy.
- The companions elaborate the body's syntax again at all. One that restated the body from `f#body`'s checked term, or a search remembered across the declarations of one recursion, would retire the lifting ([[strict-conditions]] §5) and this cost together.
- What is left in a `runtime fn` loop after this is the generator: `Sha256::expand` is 5 s with 0.3 s of it the plain function.

## Log

- 2026-11-14: Found while looking for what a cold library gate pays ([[sentinel-seed-follows-master]]); fixed for context-search defaults in the same round.
- 2026-11-17: let values in the default-goal query, the squashed probe kept (loops thread).
