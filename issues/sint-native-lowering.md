---
title: Lower signed words through the native frontend
status: open
labels: [native]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-03
---

`i8`/`i64` are `SInt(n)`, a record over `BitVec(n)`
(docs/fixed-width-integers-design.md §3), so their operations are the word's
behind a field: `SInt::add(a, b) = SInt(a.bits.add(b.bits))`. The native
frontend and `rt` read `BitVec` words; a `runtime fn` over `i64` would meet
the record constructor and projection first.

Wanted: an `i64` parameter, local and result lower to the same 64-bit
register as a `u64`, with the signed operations (`Lt`, `div`, `shift_right`,
`extend`) lowering to their signed instructions (`JL`/`IDIV`/`SAR`/`MOVSX`).
Either the frontend sees through one-field records generally, or `SInt` gets
a `datarepr` that is its field.
