---
title: A computation over Io ends with status 1 when a write fails
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-12
updated: 2026-11-16
---

`ETm` (`lib/native/runtime/rt_io.hthr`) binds a call's answer and goes
on; it has no branch on the world and no exit. So `tr` written as one
computation over `Io` (`lib/_tests/native/runtime/rt_io_lend_tests.hthr`)
keeps looping after a failed write instead of exiting 1 as GNU's does, and
its native gate (`compiled_tr_program_over_io_runs_as_gnu_tr`, the
`runtime fn tr_upper` of `lib/_tests/native/runtime/runtime_program_tests.hthr`)
leaves the `/dev/full` case out, which the builder's tr passes.

## Scope

- An exit node in `ETm` (or `ELoop`), and a branch on a word that the
  loop can end in, lowered to `Stmt`'s `Exit` and `Branch` with their
  cases of `lower_sound`; the meaning ends the world threading with
  `Exited(status)`.
- The `/dev/full` case added to the gate.

## Done when

`tr_upper::source` exits 1 on a full stdout as GNU's does, under the
soundness theorem; then the builder's tr can go.
