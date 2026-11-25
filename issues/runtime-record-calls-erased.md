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

## Log

- 2026-11-25: Round started (branch `claude/ownership-record-calls-erased`). The route, written down before building, and why each pin stays one conversion linear in the function:

  - **What the callee publishes.** A function of a laid record that takes an erased parameter (no record parameters, no read spans, not a loop) publishes, beside what it publishes today, `T::n::words(t, xs…)`: its *held* meaning written out as a closed Heather function of the record and the code's words, with no erased parameter and no span (each value bound once, a marked reader's field or element read off the record by its mark, a marked writer's store into the record, a call of another function of the record by that function, a branch). And `T::n::runs_words(own, t, length, xs…, holds)`: the same `FFun::held_agrees` as `runs_held`, with the pin `held meaning(T::n::rt, env) = T::n::words(t, xs…)`. `runs_held` is published exactly as before.
  - **Its pin is linear.** One side is the reflection's held meaning, the other a λ over the record whose body names the same marks and globals; nothing on the right has a world, an environment or a span, so the kernel unfolds the meaning once against it, as an ordinary function's pin unfolds the meaning against the function's body. Not the cheaper-looking alternative of defining `T::n::words` *as* the held meaning at a fixed span and length word: its pin would compare a meaning with a meaning at another span, environment by environment, which is the wall the plain shadow hit ([[runtime-erased-pure-shadow]], and the note above `runtime_held_ref` in `runtime.hthr`).
  - **The caller.** A call `t.n(x, p)` is reflected with its erased arguments dropped (`rt_data_args`), its operand count the data operands. Its mark is `Writer::runs(record, k, λ a ws => T::n::words(a, ws…))`, and what the mark owes is `T::n::runs_words` read along the call (`runtime_held_ran`), which takes no proof: the mark owes a proof-free statement at every word, as the plain caller's table entry `g::words` does. The code calls `T::n::bytes` as before, passing nothing for the proof.
  - **The caller's pin.** `held meaning(T::m::rt) = T::m(…)` meets `T::n::words(t, w…)` on the left where the body has `T::n(t, w…, p)`: the kernel unfolds both once per call site, the written-out body against the elaborated one, linear in the callee (the plain caller's cost, residue item of [[runtime-erased-written-out-shapes]]). The fallback that reverts each callee to a parameter reverts only callees without an erased parameter, since an erased callee's two names have to meet by unfolding.
  - **What does not change.** A function that takes no erased parameter publishes the same declarations from the same terms (the marks lists are built from the same items); `HWorld`, `Writer` and `FTm::Sem` are untouched; the helpers the writer spells with (`Reader::read_at`, `Writer::set_at`, `Writer::store_at` in `rt_held.hthr`) are new functions beside the meaning, reducing to what `Reader::value` and `Writer::state` reduce to at a literal offset. If writing out or its pin fails, the callee is published as today without `words`, and a caller is refused naming why.
