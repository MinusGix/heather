---
title: A machine that simulates a Linux tree makes only that tree's traces
status: closed
labels: [native,semantics,proofs]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-10-21
updated: 2026-11-06
---

`Sim(t)(s)` (`lib/std/os/linux/linux_x86_64_sim.hthr`) says every Linux-valid trace of `t`
runs as `s`. That is the direction a compiler proves. The milestone wants
"exactly": every `LinuxRuns(io, events, s)` of a machine that `SimProgram`s a
tree is the events of some returned trace of the tree.

## Shape

- By determinism (`linux_runs_determine` in `lib/std/os/linux/linux_x86_64_determinism.hthr`):
  walk the run's events against `p.at(n)`. At a call, the tree's call and the
  machine's request meet (`call_determines`), so the answer is one the tree
  takes. A step where the tree is cut is covered by a larger `n`.
- **What can't be proved without more**: a tree that never returns at any
  fuel (an `iter` that loops forever) while the machine exits. `Sim` is partial
  correctness, so such a machine simulates it. Either state the converse as
  "a prefix of a trace up to a cut", or wait for the kernel coinduction round
  ([[kernel-coinductive-types]]) and state divergence as a coinductive
  `Sim`.

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns `Sim`, `RunsAs` and the bridge. Assumed
  here: only that `RunsAs` is read off the shared `LinuxAnswered`/`LinuxExits`.

## Log

- 2026-10-21: `docs/kernel-coinduction-design.md` §6.1 names a kernel-free
  route for the diverging case: make a `Tau` cost the machine at least one
  step (non-stuttering simulation, CompCert's measure in its simplest form),
  so a machine that exits after `k` steps meets a tree that does something
  within `k` `Tau`s; then determinism gives the converse. Traces do not see
  `Tau`s, so this changes `Sim`'s definition (a step-wise reading beside
  `RunsAs`), not only `sim_tau`. The coinductive `Sim` stays the statement the compiler
  theorem should end with, after the kernel round.
- 2026-11-06: 2026-11-06: Done, as the Shape's "prefix of a trace up to a cut" option.
  `sim_run_of` (`lib/std/os/linux/linux_x86_64_sim.hthr`): every run of a
  machine that `Sim`s a tree, with answers Linux may give, is `RunOf` the
  tree: the events of a whole trace of it, or a prefix of them ending where
  the tree is cut (`IsCutTrace`, new in `lib/std/itree/itree_trace.hthr`: a
  trace that reached a `Cut`, not a prefix stopped early). The walk
  (`sim_related_run`) recurses on the tree and carries `SimRelated`: each
  trace's claim holds from some state related to the run's, because claim and
  run meet only up to `SameDefinedState` and each trace past an answer is
  met at a state of its own. New in the determinism module: `asks_meet` (the
  call two related states ask is one call, without an answer to compare) and
  `exits_not_asks`, both through `rax_kind`, a closed classification of
  RAX. Program forms: `Program::sim_run_at`, `Program::sim_linux_runs_at`
  (from `LinuxRuns`, whose answers are valid, `linux_runs_valid`), and
  `Program::sim_run_produces` (exact where the tree is not cut along the
  run). Probes in `lib/_tests/std/os/linux/linux_x86_64_sim_tests.hthr`
  show the cut side is needed. Divergence went to [[linux-sim-divergence]].
