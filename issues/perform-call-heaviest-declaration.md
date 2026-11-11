---
title: Target::perform_call is 33 s and 1.3 GB of the library gate, half of it omega
status: open
labels: [performance,native,proofs]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

One declaration is 4% of the whole library gate. Found while writing [[performance-overview-2026-11-11]].

`native_compile_correct::Target::perform_call`, cold, width one, release binary, 2026-11-11: 32.7 s, of which 12.2 s is the kernel gate and 16.3 s is `omega` (reflection, search and checking its certificate). The library's 23,856 declarations take 639 s in all, and the next heaviest are 12.7 s. Checking `lib/native/native_compile_correct.hthr` cold peaks at 2.3 GB, the largest of any corpus file and a third of the suite's rail: `perform_call` grows the peak by 1.3 GB on its own (`peak_growth_kb`), and `itree_trace::IsTrace::split_bind` in its closure by 0.6 GB (9.7 s, nearly all of it in the gate).

`docs/proof-patterns.md` already says what usually causes this shape: `omega` over closed layout terms, where Nat step lemmas would do (see also [[omega-per-goal-elaboration-cost]]). Nobody has looked at this proof with that in mind.

## Done when

`perform_call` is in line with its neighbours (a few seconds), by restating its arithmetic steps or by splitting it into stage lemmas, and the module's peak memory is back under a gigabyte.
