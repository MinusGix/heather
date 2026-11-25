---
title: The bytes-level language: words and references, a heap with a shadow, one meaning, placelessness as a theorem
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5, first part: the bytes-level language as the design wants it (§17.3), built beside FunctionIR's memory half. This issue is the language and its meaning; its lowering to x86 and the translation from old programs follow it in the same stage.

## Scope

- **First, a reading** (an hour, reported in the log before building): are `lib/native/function_ir/function_ir_lower_structured.hthr` and the frame proofs of `function_ir_lower_calls.hthr` generic in the body's invariant, so that the structured-control lowering and the frames can be cited by a new memory layer, or are they stated over `Buffers()` so that they must be redone? Name the theorems either way. §17.4 calls this the unknown of the whole stage.
- **Values and kinds**: `Word` and `Ref` (a block and a byte offset); every id has a kind; validity checks kinds as it checks widths.
- **The heap**: bytes per block with a shadow of entries (which eight-byte slots hold a reference and to what), canonical (zero under an entry). Grown from `lib/native/reference_cells/reference_cells.hthr`.
- **Nodes**: a wrapper over the existing word `Node` (valid only where the wrapped node touches no buffer), and through a reference a load and a store at each width, a load and a store of a reference, an offset, a typed range copy. No node names a buffer by number. Structured regions, calls and loops over these nodes, reusing the existing shapes where the reading says they can be.
- **One meaning**: `run(p, f, args, heap) → Option<Answer>` with `Answer { words, heap }` and `Calls()` as §17.2 states them; a callee kind for a system call is left as a constructor with no cases yet (the world's design is being done separately). `Refines(p, q)`: every answer of `p` is an answer of `q`.
- **Placelessness**: `run_renames`, a run commutes with a renaming of blocks, proved once for the language.
- **Site facts**: a load or a store is defined where it is in bounds, does not cut a reference, and is inside what may be written; state those as the node's definedness, so a later lowering takes them as facts.
- Probes: the experiment's program (store a reference, load it, read through it) in the real language; a window passed as a reference and a length to a callee that writes it; two windows of one block written by one callee; each with its control.

## Done when

The language, `run`, validity and `run_renames` pass the library gate with the probes, the reading's answer is in the log, and nothing in `lib/native/function_ir`'s existing modules has changed.

## What it assumes from elsewhere

- **[[x86-memory-contract]]** owns `Injected`, `Sub` and `Site::Meets`, which this language's lowering will cite.
- **[[ownership-reference-cells-spike]]** (closed) is the experiment this replaces.
