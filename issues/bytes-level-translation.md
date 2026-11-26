---
title: FunctionIR programs translated to the bytes level, and crates/linked's exports compiled both ways
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-26
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

## Log

- 2026-11-26, item 1: **the survey.** Each row's forms were counted by evaluating a census over the program compile-x86 lowers: the `_cut` program after the optimizer, read from the row's kept certificate (word-only rows lower `_program` directly). The certificates were written by `scripts/bytes-level-compare --compile-only`.

  | Row | Forms in the lowered program |
  |---|---|
  | sha512_t1, _t2, _next | word nodes, `Call` (3 functions, no buffers) |
  | sha256_t1, _t2, _next | word nodes, `Resize` (1 function) |
  | sha256_compress, _update, _finish | `BufferLoad` 8–10, `BufferStore` 11–14, `WideLoad(4)` 19–20, `WideStore(4)` 8–10, `ByteSwap` ~20, ~130 conditionals, 61–86 calls to lent callees, 9–10 bounded loops, 25–31 lent functions |
  | sha256_init | `BufferStore` 8, `WideStore(4)` 1, `ByteSwap` 1, 11 calls |
  | count_newlines, raise_span, list_raise_letters, copy_span | `BufferLoad` 2, `BufferStore` 0–2, one bounded loop, at most one call |
  | copy_window | as copy_span, and the exports' only `Lend` (two views, one written) |
  | scan_token (scan_step, scan_accept, scan_begin as entries) | `BufferLoad` 2, ~480 comparisons, ~400 conditionals, 36 calls, one loop |
  | scan_tokens | `BufferLoad` 2, `BufferStore` 8, `WideStore(4)` 1, `ByteSwap` 1, ~400 conditionals, 51 calls, two loops |

  No export uses wide accesses at 2 or 8 bytes (or any other width), `TableRead`, a `Fixed` span, levels, or `also`.

  The native gates add:
  - `also`: enum_fields, enum_payload, narrow_fields, two_words.
  - A `Fixed` span, through compile-x86's sret wrapper: three_words.
  - Levels: recursion, native_program's `LEVELS`, native_recursion (with the run-time exit 139).
  - Buffer loads and stores, bounded loops and lent calls: binary_search, sort, utf8.

  native_cat and native_tools compile through the program compiler (`native_compile*`), not FunctionIR.

  Status of each form at the bytes level:
  - Word nodes are `Compute` and lowered by the same `lower_nodes`.
  - A byte load or `WideLoad(4)` becomes `Offset` and `Load(1 | 4)`. It lowers to `ADD` then `MOVZX` or `MOV r32`, the shape the old load already emits.
  - A byte store or `WideStore(4)` becomes `Offset`, `Store` and a reload `Load`, which is the old node's output.
  - Two-byte accesses are refused by the lowering ([[bytes-level-copy-and-halfwords]]). No export uses them.
  - `Call` lowers, recursion included.
  - `Lend` becomes the views' `Offset`s and a `Call`. The old meaning clips a view at its buffer's end, so the translation states the clipped length.
  - A bounded loop becomes a plain loop with a counter, an exhausted bit, and a bound-zero branch before it.
  - `also` and `Fixed` exist in the language (a results list; a reference and a constant length).
  - Levels have no counterpart. The old meaning answers zero past the last level, while the translated meaning recurses on. The out-of-room exit has no meaning ([[bytes-level-lowering-recursion]]).
  - `TableRead` is refused by `lower_nodes` on both paths.
