---
title: State a function of spans in terms of spans, not address words and a lending
status: open
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
