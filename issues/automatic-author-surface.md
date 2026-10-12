---
title: Write a native program as itself: natural steps, split_all, defaulted obligations
status: closed
labels: [native,frontend,tactics,design]
created: 2026-10-01
updated: 2026-10-01
---

A native program should read as the program: its step at its own type, its
specification, and the proofs that are genuinely about it. The language
should discharge the routine obligations, and a failure should hand the
author the one goal left over.

Design and as-landed record: `docs/automatic-author-surface-design.md`.
Three parts:

1. `split_all` splits what blocks the goal: binders, conjunctions, any stuck
   finite match (not only comparisons). Every occurrence of the split term is
   specialized, and records are not split.
2. Fold steps: `function_ir_loop::fold_body`, plus bundles over `fold_bytes`
   in a new `read_program` module. The loop generator reflects the fold step
   directly.
3. Record fields with a default (`name: T := e`), run at the construction
   against the instantiated field type, in the declaring scope.

The acceptance was `wc_l.hthr` and `wc.hthr`: `advances`, `folds`, `step_is`
and the transports are gone, and `wc`'s executable is unchanged but for the
needle immediate.

## Follow-ups, each with an owner

- [[split-all-through-recursive-definitions]]: unfolding a recursive
  specification leaves raw recursor terms.
- [[field-defaults-under-locals]]: defaults ran only where a construction
  had no locals (closed 2026-10-12: they now run under locals).
- [[byte-vocabulary-for-native-programs]]: `==`, `<` and literals at
  `BitVec(8)`.
- [[fold-programs-carry-a-needle]]: the read profile still threads a needle
  a fold never reads.
- [[wc-words-no-break-space]]: GNU `wc` splits words at 0xA0.
- Leaf alternation (`refl` here, a contradiction there) is
  [[tactic-composition-ergonomics]]'s.

## Log

- 2026-10-01: 2026-10-01: Landed. Full suite 3148 passed. wc_l.hthr is 86 → 60 lines and wc.hthr 433 → 297. The wc executable differs from the previous build only in the needle immediate, and wc -l is 7 bytes smaller (constant compares). Follow-ups are filed above. Agreed next steps are on [[native-loop-emitting-stores]] (stream filter) and [[native-one-program-logic]].
