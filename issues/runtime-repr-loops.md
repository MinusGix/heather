---
title: Loops over repr'd words in runtime fns
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

A fuel or measured runtime fn (docs/runtime-fn-setups-design.md §16.11)
keeps its state in 64-bit words: `Fun::judge` refuses a loop whose
parameters or result are a type held by its `datarepr` (`SInt(64)`, §16.13),
with "a loop over something other than 64-bit words" for the result and the
plain parameter reason for a fuel loop's `i64` state
(`runtime_sint_tests.hthr`'s `i64_count`).

The loop theorems (`rt_loop.hthr`) are stated over `Ty::Words`; since
[[sint-native-lowering]] the environment lemmas they call take
`Ty::OneWords` (`Ty::words_one_words` bridges), so the remaining work is the
loop equations' state casts (`Ty::cast` at `Named(i)` is the repr's `abs`
of the word, `Ty::convert`) and the generator's per-word equation spelling,
which assumes each state variable is a `BitVec(64)`.
