---
title: State a function of words as the case of a function of spans lent nothing
status: open
labels: [native,theorems,readability]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

`Prog::Computes` (words) and `Prog::ComputesOver` (spans) are two contracts (`function_ir_correct.hthr`). `compiled_returns_unlent` (`function_ir_compile.hthr`) already proves that the plain one follows from the lent one at nothing lent. Stating `Computes` as `ComputesOver` at an empty lending, with the equivalence proved once, leaves one notion of what a compiled function does, for the doc and for a caller mixing the two.

Done when: the equivalence (both directions) is in `function_ir_correct`, with a probe at a function of words.

Related: [[compiled-function-implements]] (the same file, built in the same thread).
