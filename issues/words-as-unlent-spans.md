---
title: State a function of words as the case of a function of spans lent nothing
status: closed
labels: [native,theorems,readability]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-11-16
updated: 2026-11-16
---

`Prog::Computes` (words) and `Prog::ComputesOver` (spans) are two contracts (`function_ir_correct.hthr`). `compiled_returns_unlent` (`function_ir_compile.hthr`) already proves that the plain one follows from the lent one at nothing lent. Stating `Computes` as `ComputesOver` at an empty lending, with the equivalence proved once, leaves one notion of what a compiled function does, for the doc and for a caller mixing the two.

Done when: the equivalence (both directions) is in `function_ir_correct`, with a probe at a function of words.

Related: [[compiled-function-implements]] (the same file, built in the same thread).

## Log

- 2026-11-16: Done: Prog::computes_over_none and Prog::computes_of_over_none in function_ir_correct.hthr (Computes is ComputesOver at Lending::none() and the empty file; the way back entered below the stack's top); probes sum_over_none and sum_back.
