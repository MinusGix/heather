---
title: The bytes-level language on the contract's heap: one memory, a transitive refinement, Site::Meets in its final form
status: open
labels: [native,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5, second part: the bytes-level language and the machine contract made one thing. They were built in parallel ([[bytes-level-language]], [[x86-memory-contract]]) and each has its own memory type.

## Scope

- **One memory.** `lib/native/bytes_level/bytes_memory`'s `Memory` (a heap plus undefined flags behind an accessor) becomes the contract's `Heap` (`lib/std/arch/x86_64/x86_64_memory_contract.hthr`: blocks as a list, a shadow of pointers, flags), used only through its accessors. The language's operations the contract lacks (`take` and `put` with pointers and flags, `copy`, `read_bytes`) move beside the contract's own, stated over the same accessors, with the contract's `store`, `store_ref` and loads derived from `take` and `put` or the reverse, whichever leaves one definition of each. The toy language of `lib/native/reference_cells` is deleted, its probes re-expressed in the bytes-level language where they are not already there.
- **`Stuck` carries the history it was stuck after**, and `Refines`' exception reads "the input is stuck after a prefix of that history". As built, a stuck middle program makes the third clause vacuous while the first may diverge silently, so refinement is not transitive; prove transitivity (`refines_trans`) after the change, with reflexivity kept.
- **`Site::Meets` in its final form**, in the contract module, replacing the provisional one: the machine's state carries the world, and at every fuel: *done*, the routine returns with the words in place, the kept registers kept, its stores inside the lending, the answer's heap injected and the answer's world; *exited*, the exit call is made with that status and world; *going*, every world the code reaches before it returns or exits is a prefix of a history the run reaches. `Returned` becomes the language's `Answer` lowered. The probe that the old `Site::CallsLent` at one lending gives the *done* clause at an empty shadow is kept.
- **Evaluation**: `run` on the list heap at doubling program lengths, both shapes the first part measured (reads of the block just stored; reads that pass every earlier store). Both should be linear.

## Done when

One heap type and one set of memory operations serve the language and the contract; `Refines` is reflexive and transitive; `Site::Meets` has its three clauses and its probe; `reference_cells` is gone; the suite and `scripts/linked --check` pass with every existing certificate unchanged.

## What it assumes from elsewhere

- **[[lowering-generic-in-memory]]** owns generalising the existing emission theorems so [[bytes-level-lowering]] can cite them; this issue changes none of `lib/native/function_ir`.

## Log

- 2026-11-25: The coordinating branch does not carry `lib/native/bytes_level/` until this issue lands. Stage 1 ([[x86-memory-contract]]) moved the heap out of `lib/native/reference_cells` into the contract module, renamed `Entry` to `Pointer` and made the blocks a list; [[bytes-level-language]] was built in parallel on the experiment's heap as a function (`set_block(m.heap.bytes, …)`, about ninety uses). Merged, `bytes_memory.hthr` does not elaborate (`Loc`, `Entry`, `Heap` unknown) and the whole-library gate fails on it. The language and its probes are on `claude/bytes-level-language` (head as merged at a431910) and on this issue's branch, which was cut with them present; moving them onto the contract's heap is this issue's first step, and they return to the coordinating branch with it.
