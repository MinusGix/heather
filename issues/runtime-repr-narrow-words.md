---
title: Pass i8/i16/i32 across a runtime fn's boundary
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

`sint.hthr` gives `SInt(8)`…`SInt(64)` a `datarepr` each (`I8`…`I64`), but
only `I64`'s carrier is one 64-bit word, which is what a function's boundary
passes (`Ty::OneWord`, docs/runtime-fn-setups-design.md §16.13). A
`runtime fn` with an `i32` parameter is refused with "the datarepr `I32`
holds its type in something other than one 64-bit word"
(`runtime_sint_tests.hthr`'s `i32_add`).

The unsigned narrow words have the same limit today (a `BitVec(32)`
parameter is refused by the judgment). Both want the boundary to widen a
narrow word: zero-extended for `BitVec(w)`, sign-extended for `SInt(w)`
(a `Resize` at the edge, §16.12, and its signed twin from
[[runtime-signed-extend-divide]]), with `Ty::convert`'s word reading
generalised from `Word(64)` to any width.

## Log

- 2026-11-08: 2026-11-08: the signed twin of Resize exists now (FunctionIR SignResize, rt Sext), so the boundary widening this issue wants has both nodes. datarepr-value-parameter-telescope moves with this issue: one repr over SInt's width only pays once a narrow SInt can be held. SInt::extend takes an SInt(32), so it is refused until then.
