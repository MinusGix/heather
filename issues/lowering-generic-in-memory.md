---
title: The lowering's frame, call and loop theorems generic in their memory clause, with the old statements as an instance
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5: the existing lowering's frame, call and loop theorems made generic in what they say about memory, so the new memory layer cites them instead of restating them.

[[bytes-level-language]]'s reading (its log has the table, theorem by theorem): in `lib/native/function_ir/function_ir_lower_calls.hthr`, about 170 theorems are words and frame only; 8 are already generic in `keep: M → Type` (`epilogue_moves`, `result_moves`, `loop_rounds`, `loop_stops`, `loop_enters`, `loop_marks`, `loop_leaves`, `epilogue_moves_words`); and about 90 more go through `EmitsOver`, whose `Stack::Trail(…, now: Buffers())` they use only for stability under the frame's own stores (the call sequence, `call_step`, `Site::loop_passes`, `loop_emits`, `function_enters`, `function_closes`, `function_runs`, `program_step`). Without a generalisation the new lowering restates roughly that many lines.

## Scope

- **A memory clause.** `EmitsOver`, `ArgsReady`, `Called`, `Entered` and `Closed` take `Mem: S → M → Type` with one law, that it is stable under the frame's own stores (`(now) → stack.Stable(w, Mem(now))`), and `Site::loop_passes` ranges over a state type. Each of the ninety is then proved once, generically.
- **The old instance.** The existing statements are the instance at `Buffers()` and `Stack::Trail`, as abbreviations with one-line derivations, so every existing caller and every existing certificate is unchanged.
- **The new instance stated**, as a probe that the clause holds at "the stores were inside the lending and the heap is injected" (`WroteIn ∧ Injected` of `lib/std/arch/x86_64/x86_64_memory_contract.hthr`), so [[bytes-level-lowering]] cites the generic theorems at it.
- **Loops without a bound**: the reading's second table says which loop theorems survive as they are, which survive with the counter cut out (`loop_entry_sound`, `loop_rounds`), and that `Site::loop_passes` becomes an induction on the run's fuel. State the generic forms so that both the bounded loop of the old lowering and the plain loop of the new are instances; do not remove the bounded loop here.

## Done when

The generic theorems and the old instance pass the suite with every existing certificate unchanged (`scripts/linked --check`, the native gates), the new instance's probe checks, the cost of checking `function_ir_lower_calls` is reported before and after, and the log lists each theorem made generic.

## What it assumes from elsewhere

- **[[x86-memory-contract]]** (closed) gives `WroteIn`, `Injected`, `Stable`.
- **[[bytes-level-on-the-contract]]** is moving the language onto the contract's heap at the same time; this issue touches `lib/native/function_ir` and it does not.
