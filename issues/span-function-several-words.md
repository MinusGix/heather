---
title: A function over a span answering several words: what is left
status: open
labels: [native,runtime-fn,layout]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-24
updated: 2026-11-24
---

A function over a span (`FTm`), a `Bytes(n)` or a laid record answered one 64-bit word beside the span it leaves, so the arena's `alloc` answered `Full` as the word `2^64 - 1`. Minus (2026-11-24): span functions answer several words, as plain functions do.

Built (docs/native/runtime-fn-setups-design.md §16.21): a result that is a record of 64-bit words or an enum whose constructors carry them is returned in its words by the plain conventions (§16.16-17: the first word, the rest in `Function.also`), stated at the boundary by `FTm::AnswersAll`, for the span, `Bytes(n)` and laid-record routes; `runs_over`, `runs_held` and `runs_bytes` keep their shape with the result general. The arena's `alloc` and `new_vec` answer `Alloc { Got(base), Full }`, and the sentinel is gone. Probes: `lib/_tests/native/runtime/runtime_span_words_tests.hthr`, the arena rows of `runtime_ports_tests.hthr`, `arena_laws_tests.hthr`.

What is left, each refused by name:

- **A compiled caller of such a function.** A call inside a span function reads one word (`FTm::call_sound` asks `Ty::Returned`); the record route's callee world `HWorld::Runs` is one word. The plain route's `Tm::called` reads every word back (`Ty::Back`), which the span route would do over `Writers`. Until then a caller is a Heather function (`alloc_then_store`).
- **A loop answering several words**: with the loop combinator's round 4 (the loop layer states a pass at one word).
- **A `match` on an enum in a laid record's function** (`Tm::Pick` not written out over the span), and enum or record parameters of a span function.
- **`compile-x86` of a writer of several words**: refused in `runtime_shape`; its certificate would state `Prog::ComputesBoth` over the written span, and `crates/linked` would export it as a structure.
- **A narrow field or a bit slot in such a result** (`Ty::WordsOut` asks 64-bit words; the plain boundary widens them).
- **Niches** (docs/native/layout-design.md §12): an enum laid in its payload's word where the payload's type rules a value out. Designed and measured for the arena's calls, where it does not matter; to build where enums are stored in bulk.
