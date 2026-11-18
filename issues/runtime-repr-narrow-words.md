---
title: Pass i8/i16/i32 across a runtime fn's boundary
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-18
---

`sint.hthr` gives `SInt(8)`…`SInt(64)` a `datarepr` each (`I8`…`I64`), but
only `I64`'s carrier is one 64-bit word, which is what a function's boundary
passes (`Ty::OneWord`, docs/native/runtime-fn-setups-design.md §16.13). A
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
- 2026-11-18: The insertion sort over `Bytes(n)` needs it: its inner loop takes `key: u8`. A probe gave the written-out function narrow parameter types (`runtime_own_params` at each parameter's `Ty::sem`), and that part goes through. The loop then stops at two places. First, a loop's spent answer (`FFun::spent`) is the first moved state word as a 64-bit word, which a `u8` read back cannot be (zext∘trunc). Second, the verified loop lowering requires `Ty::OneWords` (`Word(64)` only, rt_lower.hthr). So the widening has to land in `Ty::OneWord` and the lowering's proofs first.
