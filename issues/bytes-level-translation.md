---
title: FunctionIR programs translated to the bytes level, and crates/linked's exports compiled both ways
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5, its last part: every FunctionIR program translated into the bytes level, and the evidence that the new layer can replace the old in one move (stage 3): every row of `crates/linked`'s exports compiled both ways gives the same assembly, or a reviewed difference.

## Scope

- **The translation**, a Heather function from a FunctionIR `Function` list and its buffer counts to a `bytes_level::Program`. Buffer `k` becomes a reference parameter and a length word (`2k`, `2k + 1`, as `Function.lent` already passes them). `BufferLoad`/`WideLoad` become an `Offset` and a `Load`. `BufferStore`/`WideStore` become an `Offset` and a `Store`. `Lend` becomes the views' `Offset`s and a `Call` on references and lengths. `Call` and `Loop` keep their shape, and word nodes are wrapped in `Compute`. A `Fixed` span is a reference whose length is the routine's constant.
- **Where the meanings differ, said once.** FunctionIR's loads read zero and its stores do nothing past a buffer's end; at the bytes level a load or a store there has no answer. A byte the old program reads past an end therefore becomes a comparison and a branch in the translation, as the old lowering already guards each such access with a comparison. A program whose stores land past an end is refused, not silently given a meaning.
- **The theorem.** Run on the heap that is the buffers (`Heap::of`, an empty shadow, `written` from the lending's marks), every `Done` of the translated program, at any fuel, is the old program's run (`function_ir_run`'s writers or the state evaluation) with the buffers read back from the answer's heap. This is stated once, over programs, and not per export.
- **The comparison.** For each row of `crates/linked`'s exports (`scripts/linked`), compile the old way and through the translation and the new lowering ([[bytes-level-lowering]]), and compare the assembly. Where they differ, the difference is listed and reviewed (a placement, a guard), and either fixed or accepted with its reason in the log.

## Done when

The translation and its theorem pass the library gate; the comparison runs over every export row and its outcome is in the log, with the differences reviewed.

## What it assumes from elsewhere

- **[[bytes-level-language]]** owns the target language and `run`.
- **[[bytes-level-lowering]]** owns the new lowering the comparison compiles through.
