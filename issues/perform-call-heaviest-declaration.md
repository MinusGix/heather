---
title: Target::perform_call is 33 s and 1.3 GB of the library gate, half of it omega
status: open
labels: [performance,native,proofs]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-14
---

One declaration is 4% of the whole library gate. Found while writing [[performance-overview-2026-11-11]].

`native_compile_correct::Target::perform_call`, cold, width one, release binary, 2026-11-11: 32.7 s, of which 12.2 s is the kernel gate and 16.3 s is `omega` (reflection, search and checking its certificate). The library's 23,856 declarations take 639 s in all, and the next heaviest are 12.7 s. Checking `lib/native/native_compile_correct.hthr` cold peaks at 2.3 GB, the largest of any corpus file and a third of the suite's rail: `perform_call` grows the peak by 1.3 GB on its own (`peak_growth_kb`), and `itree_trace::IsTrace::split_bind` in its closure by 0.6 GB (9.7 s, nearly all of it in the gate).

`docs/proof-patterns.md` already says what usually causes this shape: `omega` over closed layout terms, where Nat step lemmas would do (see also [[omega-per-goal-elaboration-cost]]). Nobody has looked at this proof with that in mind.

## Done when

`perform_call` is in line with its neighbours (a few seconds), by restating its arithmetic steps or by splitting it into stage lemmas, and the module's peak memory is back under a gigabyte.

## Log

- 2026-11-11: `Target::perform_call` no longer exists: U5's step 5c ([[native-one-compiler]]) replaced it by a call site proved once from a contract (`Target::goes_calls`, `native_compile_function.hthr`) and a callee proved entry to return (`Target::procedures_body`, `native_compile_correct.hthr`). Measured the same way (`--only`, width one, release binary, cloud box, 2026-11-11): `procedures_body` is 9.5 s with 0.1 s in the kernel gate and five `omega` calls, and it still grows the peak by 1.4 GB; `goes_calls` is 0.1 s, `function_performs` 0.3 s, `based_left` 1.1 s, `goes_counted`, `procedures_deep` and `calls_of` under 0.1 s each. So the time fell to under a third and the gate's share went, and the memory did not move: it is in elaborating `procedures_body`, not in the gate and not obviously in `omega`. The done-when reads on `procedures_body` from here; where its elaboration allocates has not been looked at.
- 2026-11-14: `native_compile_correct` is the costliest module of a cold library build (58 s of 1454 s of child time), and `Target::procedures_body` alone is 42 s of it (24 s in the gate, 25 M steps), with `native_compile_correct_calls` at 11 s and `native_compile_correct_bare` at 7 s.
