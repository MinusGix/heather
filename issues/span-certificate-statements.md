---
title: State a function of spans in terms of spans, not address words and a lending
status: closed
labels: [native,theorems,readability,exports]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-16
updated: 2026-11-16
---

A certificate for a function of spans takes `addresses`, `Lending::writing(counts, addresses, file, marks)`, a `Loan`, the span's address and length as raw words among `[a0, a1, …]`, and answers `Ending(word := f(…).value, buffers := Cons(f(…).after, rest))` (`Prog::ComputesOver`, `function_ir_correct.hthr`). What it means is what Rust's signature says: given a `&mut [u8]` at some address holding `bytes`, the code returns `f(bytes, …).value` and leaves `f(bytes, …).after` there.

Wanted: a `Span { at, bytes }` (or the like) and a statement over a list of spans and the words, with the lending, the argument words and the ending built from it, so SHA-256's certificate reads like its Rust signature. Design questions: where `marks` (read or written) live, views lent between functions (`compiled_returns_marked`), and what the `Loan` premise becomes (a separation statement over the spans and the stack). A short design note before building.

## What it assumes from elsewhere
- **[[compiled-function-implements]]** owns the per-function form for words; assumed here only that the span form should read the same way.

## Resolution (2026-11-16)
Built as `Slice`, `Borrow` (`Shared`/`Mut`), `Prog::ComputesOn` and `Prog::ComputesInto` in `lib/native/function_ir/function_ir_borrows.hthr`; design and decisions in `docs/native/span-statements-design.md`. `compile-x86` states every span certificate's `_returns` this way and keeps the statement over any file as `_returns_over`. The names are not `Span`/`Lent` because records of those names are already imported by certificates. Marks are the borrow's constructor; views do not appear in the exported function's statement; the `Loan` stays a premise under the name `Machine::Lends`.

Left: deriving `Machine::Lends` from disjointness of addresses over the byte memory model ([[span-footprint-automation]]), and a curried form once [[compiled-function-implements]] settles its shape.
