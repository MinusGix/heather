---
title: A constructor's type annotation was unfolded at every constructor a computation built
status: closed
labels: [kernel,evaluator,performance,native]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

Found by profiling the kernel's check of a native tool's emission statements (`{p}_e_#`), after [[native-tool-compile-attribution]] left the evaluator as what a cold `write-elf` mostly is.

## What it was

A constructor written with its type, `pair@(T; a; b)` or `inl@(T; a)`, evaluates `T` to the Σ or sum it names, so the value it builds is the one the annotated spelling builds (`Eval::step_intro`). The elaborator writes `T` at the outermost layer of every constructor of a declaration, as a call of the declaration's type code (`El(D#tycode)`). So each `True`, `Inl`, `Cons` a computation built evaluated that call, unfolded the code (a counted step) and decoded it, to reach the same former every time.

On six of `sort_tool`'s `e_#` statements (callgrind, release binary): 192 thousand such evaluations in 2.9 million evaluator steps, and 8% of the evaluator's and the value arena's instructions.

The same profile says the rest is flat. No function of the machine is over 2% of the run by itself; a counted step is about 3.6 work items, 4.5 arena allocations and 1,200 instructions.

## Fixed

`ValueArena::memo_former`: the former a closed annotation unfolds to is kept for the arena, keyed by the annotation's syntax (and, as `TmClo::closed_ident` does, the global offset, and the environment's length when the type holds a weakening). It is the argument `memo_closed` already makes for terms: a type that reads nothing of its environment denotes one former wherever it is read. An annotation that reads the environment is evaluated as before. `a_closed_annotation_is_unfolded_once` (kernel unit test) holds both halves.

## Measured

`scripts/bench-probes --heavy --filter native/elf-cold`, four-core cloud box, dev-profile binary at width one, two samples a side in the same hour (after, before, after), minimum of the samples:

| case | before s | after s | steps before | steps after |
|---|---|---|---|---|
| `native/elf-cold-sort` | 41.44 | 38.24 | 61,481,807 | 57,618,999 |
| `native/elf-cold-head-n` | 17.81 | 16.74 | 19,843,378 | 18,897,152 |
| `native/elf-cold-tac` | 27.95 | 28.34 | 39,792,738 | 37,657,192 |
| `native/elf-cold-yes` | 5.30 | 5.66 | 1,103,644 | 1,202,722 |

Steps fall 5 to 6% on the three tools that compute. Seconds follow on `sort_tool` and `head_n_tool` and do not on `tac_tool`, whose two sides are inside each other's spread; by module, `sort_tool`'s certificate gate is 14.10 to 13.41 s and its parts' reads 10.45 to 9.38 s. `yes_tool` is slower by a store difference and not by the change: the after side's freshly warmed store has no statement verdicts for `x86_64_asm_table` (only a replay records them, [[native-process-fixed-cost]]), so each of its samples re-checks `LabelTable::item_lands_by` and its neighbours, 134 thousand steps and about 0.35 s that the before side's long-used store does not pay. The same 0.35 s sits in the other three after rows.

## Looked at and left

An application's Π annotation is two type closures built at every `app`, read only when the application stays stuck and is read back (a fifth of what a step keeps in the arena). Holding the syntax instead trades the two allocations for reference counts on every copy and drop of the elimination; the estimate was under 3% of the evaluator, so it is not done.

## Verification

`scripts/test --pr`: `== suite: 3711 passed, 0 failed, 2 ignored ==` (a kernel change, so every target and every native gate). `scripts/bench --check` reports the same uniform 1.3 to 1.9× slowdown, on `level/equiv` and `subst` as much as on the evaluator's cases, at this commit and at the one before it on the same box in the same hour, so it reads the box and not the change; no baseline was re-recorded.
