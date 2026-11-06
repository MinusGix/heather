---
title: A machine that simulates a Linux program diverges only where the program does
status: open
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
