---
title: Call runtime fns whose signature holds a repr'd type
status: closed
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

Since [[sint-native-lowering]] a runtime fn's own boundary may pass a type
held by its `datarepr` in one word (`i64_add(a, b: SInt(64)) → SInt(64)`,
docs/native/runtime-fn-setups-design.md §16.13), but a *call* of such a function is
refused: `Tm::judge` asks every callee's `Sig::is_words`, which is words or
counts only. `lib/_tests/native/runtime/runtime_sint_tests.hthr`'s
`i64_twice` is the refusal.

Two things stand in the way:

- **The caller's table must name the callee's repr.** Each runtime fn's
  world has its own `tys` table (`RecInfo::cons` of `RecInfo::word_repr`s,
  in the order its signature meets them). A call's `Sig` reads `Named(i)` at
  the *caller's* table, so the caller must collect the reprs of its callees'
  signatures too (today `runtime_reprs` reads only its own signature).
- **Linking compares tables by conversion.** `Compile::part`'s `linked`
  equates the program's sources with each instance's
  `c.world.uncurried()`; two instances whose tables number the same repr
  differently still uncurry to the same word functions, so this should
  convert, but it is unchecked.

The `Tm::lower_sound` call case already passes and returns 64-bit words
(`Ty::OneWord` covers both sides of the boundary), so the proof side is
expected to be a judgment change plus the table above.

## Log

### 2026-11-08 — done (round 2 of [[sint-native-lowering]])

docs/native/runtime-fn-setups-design.md §16.13, "Round 2": the walk finds repr'd
types as it meets them (`rt_with_reprs`), calls pass and return a record
held in one word (`Sig::Words` over the table, `RecInfo::back`), and each
function keeps its own table, linking by conversion. Probes in
`lib/_tests/native/runtime/runtime_sint_tests.hthr` (`i64_twice`,
`u64_via_i64`, `u64_sar_signed`).
