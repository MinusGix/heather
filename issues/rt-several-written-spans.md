---
title: rt: a computation that writes several spans, so a runtime fn lends two written windows (split_at_mut)
status: open
labels: [native,runtime,memory]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

An `FTm` computation writes one span: its meaning threads one list of bytes (`FTm::Sem`, `lib/native/runtime/rt_file.hthr`), and what the program's computations are answered with says so (`FTm::CallsAgree`, `rt_file_lower.hthr`: a callee leaves `Cons(m.after, rest)`, the rest unchanged). So `split_at_mut` with both halves written cannot be said in a `runtime fn`: the caller can lend two written windows of its span only to a callee that writes two spans, and no `rt` callee does. Below `rt` nothing is missing: FunctionIR's `Lend` puts back every written view in order (`put_views`), `views_apart` decides the pair, and `Loan::view_windows_reads` is stated for any set of windows ([[views-of-one-buffer-apart]], probe `splitting` in `function_ir_lower_views_tests.hthr`).

Found by [[rt-window-of-the-written-span]], whose step 2 this was: its step 1 (a window to read of the written span) needed no change of the meaning, and this one cannot be made in `rt_file*` alone.

## What it takes

- **The meaning threads the written spans.** A computation writes its first `w` spans (`FFun.writes`, default 1), and its meaning is over a file of them: `Spans → … → Mutated<Spans, value>`, `Spans` the first `w` spans. `Put` names the span it stores into. `FTm::Lend`'s written views are its first `w'` views, each a window of one of the caller's written spans, and the meaning puts back each window the callee left, in order (`List::put_window` per view, as `put_views` does).
- **`Sig` or `fsigs` carries the count**, so that `FTm::get` answers a callee at its own number of written spans; `FTm::CallsAgree` states the callee's written spans after and the rest unchanged.
- **Every consumer of `FTm::Sem` moves with it**: `rt_file_lower` (the once-proofs), `rt_file_loop`, `rt_bytes`, `rt_bytes_loop`, `rt_held`, `rt_held_loop`, the generator (`runtime.hthr`, `runtime_file.hthr`) and its statements (`runs_over`, `FTm::end_of`). Keeping `w = 1` definitionally the old type (a `Spans(1)` that reduces to one list) keeps the existing statements, but every proof at an open signature sees the change.
- **The reflector** reads a function with several `mut` spans (or a `Mutated` of a tuple of spans), each threaded through its own chain.

This crosses the loop modules [[loops-on-one-combinator]] is moving and the generator, so it waits for those to settle; rung 2 does not need it ([[rung2-spans-design]] §6: every customer fits one written span).

## Done when

A `runtime fn` that lends two apart windows of its span to a callee that writes both compiles and is stated against its run, with overlapping written windows refused by name as the control.
