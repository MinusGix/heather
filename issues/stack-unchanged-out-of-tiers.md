---
title: Stack::Unchanged and store_below leave the memory tiers before stage 3 deletes them
status: open
labels: [native,function-ir,memory]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The generic call theorem of `lib/native/function_ir/function_ir_lower_calls.hthr`, `call_step_by` ([[lowering-generic-in-memory]]), survives §17.5's stage 3 of `docs/language/ownership-design.md` (the bytes-level lowering cites it), but proves that the words passed on the stack survive the return address's store through `Stack::Unchanged` and `Stack::store_below`, which live in `lib/std/arch/x86_64/x86_64_memory_tiers.hthr`, the module stage 3 deletes. They reach it through `Stack::passes_unchanged` (`x86_64_stack_runs`), so the dependency is the stack's, not the lowering's.

Its other tier citations were moved to the contract in the same round (`Stack::wrote_in_word`, `Stack::wrote_in_widen`), as were `function_closes`'.

## Done when

`Stack::Unchanged` and `Stack::store_below` either move out of the tiers module into the stack's own (they are about the stack's words, not about what a call may store) or `Stack::passes_unchanged` is restated as a frame-rule consequence (`Stack::wrote_in_frame` at the stable predicate "the passed words read so"), and no generic theorem of `function_ir_lower_calls` names a tier. Every certificate unchanged.
