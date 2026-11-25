---
title: References held across calls: the file in FunctionIR's call contracts with a shadow
status: closed
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

FunctionIR's calls thread the file a program reads and writes as `Buffers()`: `Effects()` relates the file before a call to the file after (`function_ir_stage`, `function_ir_writes`), and the contract a compiled function meets states it in memory (`Stack::CalledOver`, `Stack::AnsweredOver`, `Site::CallsOver`, `Site::CallsLent`, the `Trail` of a body; `function_ir_lower_calls`). A program that keeps a reference in memory across a call needs that file to carry the shadow of [[ownership-reference-cells-spike]], and nothing about the shadow is in those statements.

The experiment showed the memory relation itself is additive: an empty-shadow heap injected is `Stack::InMemory`, both ways (`in_memory_injected`, `injected_in_memory`, `lib/native/reference_cells/reference_cells_bridges.hthr`), and the toy's store theorem gives `in_memory_span`'s conclusion (`in_memory_word_stored`). The file *type* in the contract is not: `Effects()` is over `Buffers()` in about 90 places across ten `function_ir` modules (33 in `function_ir_lower_calls`).

## Choices

- **Generalize**: the file becomes a heap (bytes and shadow); the contract theorems are restated over it once and today's statements are their instances at `Heap::of`. A statement change to the call machinery, every existing certificate kept through the instance lemmas.
- **Restrict first**: references are held only in blocks no call is lent (a frame slot, a block carved inside the function); calls keep `Buffers()`. Additive, and enough for a body that builds and reads a structure locally; refuses a callee that reads a stored reference.

Lean: restrict first (it is what package 5 can deliver against today's statements), then generalize when a customer passes a structure holding references to a callee.

## Done when

A function that stores a reference into a block lent to a callee, and a callee that reads through it, compile with their theorems; or the restriction is stated and enforced by the lowering with a refusal naming it.

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** owns the injection (`Injected`) and the toy's store theorems. Assumed here: only that the injection at an empty shadow is `Stack::InMemory`.

## Log

- 2026-11-25: 2026-11-25: Closed, superseded ([[bytes-level-on-the-contract]]): the generalising route was taken, at the bytes level rather than in FunctionIR. A call there is an ordinary call on values over the one `Heap` (`x86_64_memory_contract`, a shadow of references included), under `Site::Meets` (`x86_64_call_contract`), so a reference stored in a block lent to a callee is read through by the callee as by any code. FunctionIR keeps `Buffers()` until stage 3 deletes its memory half; `Heap::of` and `in_memory_injected` remain its instance at an empty shadow. The compiled case is [[bytes-level-lowering]]'s.
