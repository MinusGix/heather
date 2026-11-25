---
title: A compiled caller of a function of a record with erased fields
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

[[runtime-record-erased-fields]] compiles `Heap::read`, `Heap::store` and `Heap::reset` as `runtime fn`s of the heap, but a compiled function of the heap that calls one of them (a vector push over handles calling `Heap::store` with a proof read off `VecOk`) is not taken: the caller's walk meets `Heap::read(h, w, i, …)`, whose operands are the record `h` and a record parameter `w`, and its mark names a callee of the laid record by `T::n::words` over the record and words (`rt_held_callee`, `HeldCall`). What it needs: the callee's call read as a call of the laid record's function, its record `h.arena` (already the record the walk recognises, `Known::laid_local`) and the record parameter's word fields as its operands (`FieldWord`), and the callee's `words` written out over the arena (`runtime_held_words` already runs for these functions, since they take erased parameters; whether it succeeds for them is not checked yet). Customer: [[arena-handles-push-and-new-vec]].

## What it assumes from elsewhere

- **[[runtime-record-erased-fields]]** owns the callee's reading.
- **[[runtime-record-calls-erased]]** owns a record function calling one that takes an erased parameter (`T::n::words`).
