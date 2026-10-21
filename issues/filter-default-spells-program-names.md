---
title: Filter's advances default spells program names its scope cannot see
status: closed
labels: [native,tactics,ergonomics]
area: heather-in-heather
created: 2026-10-02
updated: 2026-10-21
---

`Filter`'s `advances` default (`{ split_all; all_goals { omega } }`) is
elaborated in `filter_program`'s scope (record field defaults resolve names
in the declaring scope). When split_all cannot find a comparison, it falls
back to splitting a neutral the source can spell, and spells it qualified:
`wc_l_eq::newline(byte)`. That module is not visible from `filter_program`,
so the default fails with "`t_dbg_wcl::newline` is qualified by
`t_dbg_wcl`, which is neither an imported module nor a type in scope", and
the error prints a raw kernel term.

Found twice on 2026-10-02: a predicate written as `eq_bit` (no match), and
one written with `∨`/`¬` decisions. Every program then has to give
`advances := …` by hand.

Wanted: split_all's spellings resolve wherever the goal came from, for
example spelled in the construction's scope or through absolute names, or a
default runs with the construction's module visible. The error should not
print raw kernel terms.

## Log

- 2026-10-03: 2026-10-03 (S4): both cases reported here are fixed. A helper that is a comparison (`newline(b) = b.eq_bit(10)`, a decide_bit predicate) is now split at the comparison, which any scope spells, so wc's and wc_l's bundles take the default `advances`. What remains is a split on a program-defined neutral that is not a comparison (a Bool helper the search cannot see through), still spelled qualified by the program's module; and the error still prints a raw kernel term.
- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.
