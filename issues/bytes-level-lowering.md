---
title: The bytes level lowered to x86 under Site::Meets, proved once
status: open
labels: [native,function-ir,x86,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5, second part: the bytes level (`lib/native/bytes_level/`, [[bytes-level-language]]) lowered to x86 under the contract stated once (`Site::Meets`, `Injected`; [[x86-memory-contract]]), with its theorem proved once for every program, beside FunctionIR's lowering and not through it.

## Scope

- **The register invariant at the lowered values.** A word id holds its word as today (`File::Represents`, `Held`); a reference id holds its target's address under the injection (`Value::lower`, as the experiment found: the kind lives in the value, not the register file). Validity's kinds (`Program::valid`) are what make a wrapped node's FunctionIR equation hold of the lowered values: no word node reads a reference.
- **Leaves.** A run of `Compute` nodes is FunctionIR's leaf, lowered by `lower_nodes` and proved by `lower_nodes_keeps`/`lower_nodes_guards` unedited, at `NodesHold` over no buffers (a pure node's evaluated step satisfies its equation: `Node::holds_of`). Each memory node lowers to one instruction through the reference's address: a load or a store of 1, 2, 4 or 8 bytes (`MOV`/`MOVZX`), a reference's load and store (`MOV`, as a word's), `Offset` as an `ADD`/`LEA`, and `Copy` as a byte loop or `REP MOVSB`. Each is proved from bytes_memory's site facts (`Memory::take_some`, `put_some` and their corollaries) and one `Injected` lemma for `take` and one for `put`, since every operation is one of the two.
- **Control and calls.** Branches and loops reuse `StructuredRegion`'s emission (the label scheme, `File::meet`, `LoopRegisters`, `loop_entry`, `loop_exit`) and cite the theorems the reading found to be about words and control (`emits_seq`, `branch_emits`, `loop_rounds`, `epilogue_moves` and the rest in [[bytes-level-language]]'s log). A call is an ordinary call on values under `Site::Meets`. A window is two parameters, so nothing renumbers memory.
- **One decision first, the coordinator's.** The reading found that the call sequence, the loop's passes and the function's frame in `function_ir_lower_calls` reach memory only through `Stack::Trail`, and only for its stability under the frame's own stores. Either `EmitsOver` and its four companions (`Stack::ArgsReady`, `Called`, `Entered`, `Closed`) and `Site::loop_passes` are made generic in a state type and a memory clause with that one law (then this lowering restates none of them), or this lowering restates them over `WroteIn ∧ Injected`. The log of [[bytes-level-language]] states the generalisation exactly.
- **The heap's home.** `Memory` (the experiment's `Heap` and `written`, the blocks a run may store into) folds into the heap type [[x86-memory-contract]] moves beside `Injected`. `Injected` then asks `written(b) → spans.written(b)` and reads no byte under an entry, which is zero by `Memory::Canonical`.

## Done when

`lower_correct` for programs: whatever the placement, a program the lowering returns, resident anywhere under `Site::Meets`, answers each routine's `run` (its answer in place, its heap injected after). The bytes level's probes compile, each with its theorem, and the experiment's modules (`reference_cells*`) can be deleted.

## What it assumes from elsewhere

- **[[bytes-level-language]]** owns the language and its meaning; assumed here, only `run`, the site facts and validity as built.
- **[[x86-memory-contract]]** owns `Injected`, `Sub` and `Site::Meets`.
