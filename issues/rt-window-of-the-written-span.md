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
