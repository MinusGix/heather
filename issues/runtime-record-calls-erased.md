---
title: A function of a laid record calling one of the record that takes an erased parameter
status: open
labels: [ownership,native,runtime-fn]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`runtime fn T::m(self t: T) → u64 { t.get(0, 0) }`, where `T::get` takes a found proof, is refused by name ("a call of a function of a laid record that takes an erased parameter … is not taken yet", `rt_held_callee` in `rt_held_reflect.hthr`; probe `Slots::get_first` in `lib/_tests/native/runtime/runtime_erased_tests.hthr`). Split out of [[runtime-erased-pure-shadow]], which built the plain shapes: a function of words and a span writer that take one, their compiled callers, and a function of a laid record calling a *plain* function that takes one (`Slots::halve`).

## Why it is not the plain route

A caller's held meaning names a record callee by its mark, `Writer::runs(record, k, λ a ws => T::n(a, ws…))` (`runtime_held_run`), and what the mark owes is `HWorld::Runs` at *every* record and every word, discharged by `T::n::runs_held` (`runtime_held_ran`). With an erased parameter the mark has no proof to give `T::n` at an arbitrary word, and `runs_held` takes one. A plain callee did not have this problem because a plain caller's table lists a closed function of words (`g::words`) and owes nothing per entry beyond the callee's instance.

## The route proposed

Mirror the plain route one level up: the callee publishes a function of the record and its words with no erased parameter, its held meaning written out (`T::n::words(t, ws…)`, the record-level counterpart of `f::words`), and states its `runs_held` against that (for every word, by the same `FFun::held_agrees` with the pin `held meaning = T::n::words(…)`, which needs no proof since it is written out from the reflection); `runs_held` at `T::n` and a proof then follows by the one conversion `T::n::words(t, ws…) ≡ T::n(t, ws…, ps…)`. The caller's mark is `T::n::words` and owes the proof-free statement. What has to be written out is the held meaning's field reads and stores at the record (the accessors' marks), which `RtWriting` does not do yet.

## Done when

`Slots::get_first` compiles, its `runs_held` is published, and the refusal moves to a row.
