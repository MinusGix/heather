---
title: A measured principle's found-proof lifting re-elaborates its scope per query
status: open
labels: [tactics,performance]
area: tactics
created: 2026-11-24
updated: 2026-11-24
---

Found measuring [[branch-equations-silent-without-logic]]'s cost note.
A `decreases` function's companions are built when it is declared, and in
`lib/native/runtime/word_map.hthr` they are most of the module's cold
check. Stage times of one uncached `heather check` (width-one stopwatch
around each stage in `elab_measure_decl`, 2026-11-24; shapes, not
budgets):

| function | own lowering | `f_unfold`/`ext`/`irrel` | `f::step` | branch equations | `f::induct` |
|---|---|---|---|---|---|
| `shift_at` (6 leaves) | ~3 s | ~20 s | ~1.5 s | ~11 s | ~57 s |
| `insert_at` (6 leaves) | <1 s | ~5.5 s | <0.5 s | ~4.7 s | ~12 s |
| `find_at` (5 leaves) | <1 s | ~5 s | <0.5 s | ~2.7 s | ~5.5 s |
| `remove_at` (5 leaves) | <1 s | ~6 s | <0.5 s | ~3 s | ~4 s |

What dominates is `shift_at`'s principle, and inside it
`measure::lift_found` over the generated principle (~45 s): the principle
is a `decreases` theorem whose IH arguments inline the shift's
`m with { keys = m.keys.put(i, m.keys.at(j)), … }`, and the lifting pass
asks each call that leaves a proof to a context search for its goals.
It makes 7 goal queries (`default_goals`, ~5.3 s each, each finding one
goal) and 10 scrutinee-type queries (`scrut_ty`, ~1.4 s each), and every
query elaborates the walk's whole telescope (24–26 binders, several of
them `WordMap`-valued `with` updates) in isolation. Skipping calls that
already carry an `f#found_N` argument changed nothing: the seven calls
are ones the function's own lift did not cover (the principle's own
spelling of the IH arguments), so the cost is per query, linear in the
scope it re-elaborates.

## Wanted

The principle's found proofs reused from the function's (`f#found_N` at
the same call, the IH argument being the function's call argument), or
the query's telescope elaborated once per walk and extended, not rebuilt
per query. Then measure `word_map.hthr` again: the companions'
`f_unfold`/`ext`/`irrel` (~37 s across the four) are the next cost.
