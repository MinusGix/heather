---
title: State the compiler's theorem closed under the optimizer's refinement
status: open
labels: [native,theorems,readability,optimizer]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

`ProgramRewrites(old, new, f)` (`function_ir_stage.hthr`) is a preorder (`ProgramRewrites::then`). The return theorems have four `_through` copies (`compiled_returns_lent_through`, `compiled_returns_unlent_through`, `Ending::returns_written_through`, `Ending::returns_marked_through`).

Wanted: the theorem stated once over a program and a refinement of it, e.g. `compiler_correct_through` in `function_ir_correct.hthr`, so a certificate reads as the plain theorem plus one step of refinement, and the `_through` copies become corollaries or go.
