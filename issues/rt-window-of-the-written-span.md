---
title: rt: lend a window to read, or a second window to write, of the span a call writes
status: open
labels: [native,runtime,memory]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
---

FunctionIR now lowers views of one buffer, any of them written, where the path knows them apart ([[views-of-one-buffer-apart]]: `views_apart`, `ViewsApart`, `Loan::view_windows_reads`). The `rt` side does not reach it: `rt_file_viewed` (`lib/native/runtime/rt_file_reflect.hthr`) refuses "a window to read of the span the call writes", and an `FTm` computation writes one span, so `split_at_mut` with both halves written cannot be said in a `runtime fn` at all ([[rung2-spans-design]] §6).

## What it takes

- The reflector's refusal lifted where the windows' bounds are ordered on the path (one window's end the other's start, the `split_at` shape), the `FTm::Lend` it emits carrying views of the written span beside it; the FunctionIR check then decides apartness as it does now.
- Two written windows of the written span: the meaning of `FTm::Lend` puts back each (FunctionIR's `put_views` already does, in order).
- Stay clear of the reflector work of `runtime-erased-parameters` while it is moving.

## Done when

A `runtime fn` that lends the bytes before `mid` to read and the bytes from `mid` to write of the span it writes compiles and is stated against its run; then the same with both written.

## Log

- 2026-11-25: Second wave of `docs/language/ownership-design.md` §12: taken as its own round. The reflector work of `runtime-erased-parameters` has landed, so the caution about it in "What it takes" is spent; the session on [[runtime-erased-pure-shadow]] works in the generator and `rt_reflect.hthr` at the same time.
- 2026-11-25: Step 1 landed: a `runtime fn` lends a window to read of the span the call writes beside the written window. What it took was less than "What it takes" expected: the meaning (`FTm::lent`) already read every view after the first off the file as it is at the call, `Cons(own, rest)`, and the lowering's once-proof (`FTm::lend_ran`) puts back only the first view and is indifferent to which span a read view is of, so neither changed. The refusal was the reflector's alone: `rt_file_viewed` (`rt_file_reflect.hthr`) now takes a window after the first of any span, the written one as it is now (`rt_span` still refuses the span as it was). Apartness stays where [[views-of-one-buffer-apart]] put it, in the function compiler (`views_apart`), per function and proved once: one's end the other's start, a comparison an arm took, or two constants in order. One reflector change was needed beside it: each occurrence of a literal is bound afresh (literals are kept out of the memo), so a split at a constant gave the read window's end, its length word, the written window's start and the test four variables, the length check refused, and the function compiler's facts (about variables, not values) could not bound the windows. `RSt::reuse_literal` makes a window's bound or length word that is a literal the walk just bound reuse an equal literal bound before; it applies only there (`rt_file_word`), so no other reflection changes. Probes (`lib/_tests/native/runtime/runtime_span_split_tests.hthr`, callee `copy_byte`): `shift_at` (open `mid`: reflects as `Lend(0, [FView(0, 4, Some(2), 3), FView(0, 4, None, 2)], …)`, pinned by `shift_at_views`; runs on bytes four ways; `shift_at_stated` at every file; lowers; `shift_at_carries`, the machine code at any span and words answering `shift_at`'s value and leaving `shift_at`'s span, the checking position), `shift_two` (literal split 2, lowers), `shift_gap` (bounds ordered by a comparison an arm took, a gap between the windows, lowers); controls `shift_over` (the read window runs to the end: its meaning stated at every file, the lowering refused, `shift_over_why` naming the two views) and `shift_backwards` (the comparison the wrong way, refused, `shift_backwards_why`). `reads_own` in `rt_file_lend_tests.hthr`, the old refusal's probe, now reflects (`reads_own_reflected`). Decision: the reflector does not check apartness itself (it would duplicate the function compiler's check without its facts); the overlapping call reflects, means what it says, and is refused at compile, by name. Met on the way: a window to read's end must be compared with the span's length by its own arm (no transitivity through another bound), as [[views-of-one-buffer-apart]] recorded, so `shift_gap` tests `n <u low` beside `high <u low`.
- 2026-11-25: Step 2 not built: filed as [[rt-several-written-spans]]. Two written windows of the written span go to a callee that writes two spans, and an `FTm` computation writes one: its meaning threads one list (`FTm::Sem`) and `FTm::CallsAgree` has every computation leave the rest of its file unchanged, so no `rt` callee can take both halves to write, whatever `FTm::Lend`'s meaning puts back. Making one changes `FTm::Sem`, which every span module reads (`rt_file_lower`, `rt_file_loop`, `rt_bytes`, `rt_bytes_loop`, `rt_held`, `rt_held_loop`) and the generator (`runtime.hthr`, `runtime_file.hthr`): the loop modules [[loops-on-one-combinator]] is moving and the generator [[runtime-erased-pure-shadow]] is changing. Per the round's rule (stop where a choice changes another package) it is reported, not begun. Below `rt` nothing is missing.
