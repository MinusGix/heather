---
title: A machine that simulates a Linux program diverges only where the program does
status: closed
labels: [native,semantics,proofs]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-11-06
updated: 2026-11-06
---

`sim_run_of` (`lib/std/os/linux/linux_x86_64_sim.hthr`, from
[[linux-sim-every-machine-run]]) says every run of a machine that `Sim`s a
tree is the events of a whole trace of the tree, or the tree is cut after a
prefix of them. The cut side is not vacuous: a loop that goes round
silently is simulated by every machine, one that exits included, and at
every fuel it is cut before every run (`spin_simulated`,
`spin_cut_before` in `lib/_tests/std/os/linux/linux_x86_64_sim_tests.hthr`).
`Program::sim_run_produces` gives the exact statement only where the tree
is not cut along the run at some fuel, which a client must show.

This issue owns the exact converse: a machine that simulates a program
makes only runs the program produces, with divergence matched to
divergence.

## Shape

`docs/kernel-coinduction-design.md` §6.1 names the two routes.

1. **Kernel-free: a `Tau` costs the machine a step** (non-stuttering
   simulation, CompCert's measure in its simplest form). A tree with `n`
   `Tau`s before its next event forces `n` machine steps, so a machine
   that reaches a syscall after `k` steps meets a tree that does something
   within `k` `Tau`s, and `sim_run_of`'s walk can pick a fuel at which the
   tree is not cut. Traces do not see `Tau`s, so this is a step-wise
   reading of `Sim` beside `RunsAs`, and every producer of `Sim` (the
   native compiler, `lib/native/native_compile_correct.hthr`'s loop arm
   through `sim_tau`) must pay a step per `Tau`.
2. **Coinductive `Sim`**: a relation between the machine's runs and a
   coinductive tree (`lib/std/itree/coitree*.hthr`), so divergence meets
   divergence directly. This is the statement a compiler theorem wants to
   end with.

Which route, and whether `Sim` changes for its producers, is Minus's call.

## What it assumes from elsewhere

- **[[linux-sim-every-machine-run]]** owns the walk (`sim_related_run`).
  Assumed here: only that it stops exactly where the tree is cut.
- **[[kernel-coinductive-types]]** owns the coinductive tree the second
  route would use.

## Log

- 2026-11-06: 2026-11-06: Done, by the coinductive route (Minus asked to do the issue;
  the route card recommended it). `LinuxSimCo(io)(t, s)`
  (`lib/std/os/linux/linux_x86_64_sim_co.hthr`) is a codata relation between
  a `CoTree` and a machine state, shaped like `Eutt`: each node may drop
  finitely many tree `Tau`s for free, then the machine steps to the exit
  (`SimExits`), takes at least one step for a `Tau` (`SimSteps`,
  `LinuxPlus`), or steps to the syscall requesting the call and holds again
  from every way Linux may answer and resume (`SimCalls`, over a
  `LinuxResumption` record, since a recursive field takes one argument).
  Results: `LinuxSimCo::sim_program` (it is `SimProgram` of
  `CoTree::program`, so the finite clients keep working), and the exact
  converse `LinuxSimCo::run_produced`/`linux_runs_produced`: every run with
  valid answers is the events of a returned trace the tree produces. The
  walk recurses on the run's events and, within a segment, on a fuel bounding
  its steps: a paid `Tau` peels at least one machine step
  (`linux_steps_peel`, new in the determinism module). Divergence:
  `LinuxSimCo::spin_no_run` (a machine simulating `spin` has no run) and
  `LinuxSimCo::forever` (a machine that goes round an invariant forever
  simulates `spin`). Probes in
  `lib/_tests/std/os/linux/linux_x86_64_sim_co_tests.hthr`. The compiler
  proving `LinuxSimCo` went to [[native-compile-co-sim]].
