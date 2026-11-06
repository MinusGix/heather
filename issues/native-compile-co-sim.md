---
title: Prove compiled programs simulate their source's fuel-free tree
status: closed
labels: [native,semantics,proofs,coinduction]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-11-06
updated: 2026-11-06
---

`LinuxSimCo` (`lib/std/os/linux/linux_x86_64_sim_co.hthr`, from
[[linux-sim-divergence]]) relates a coinductive tree to the machine with
an exact converse: every run of the machine is a returned trace the tree
produces, and a machine that simulates a tree that never returns has no
run. It is `Sim` at every depth (`LinuxSimCo::sim_program`), so a compiler
that proves it keeps every client of `SimProgram`.

The native compiler proves `SimProgram` over a source's fuelled denotation
(`lib/native/native_compile_correct.hthr`, `Target::goes_repeat` and the
ELF theorems). This issue owns proving `LinuxSimCo` over the fuel-free one,
`Source::tree_co` (`lib/native/native_source_co.hthr`), so a compiled
program's theorem says its runs are exactly the source's and a source loop
that never ends compiles to a machine that never ends.

## Shape

- Each `Tau` the relation does not drop costs the machine at least one
  step (`LinuxPlus`). A compiled `Repeat` jumps back once a pass, so its
  `Tau` is paid by the `JMP`; finitely many other `Tau`s per node may be
  dropped for free, as `Eutt` drops them.
- The relation is coinductive, so the loop rule is a corecursion over the
  loop's invariant, as `LinuxSimCo::forever` is for `spin`, not an
  induction on fuel.
- `LinuxSimCo` has no bind or iteration rules yet (`back` only); the
  compiler round adds the ones it needs, generically over the tree, beside
  `sim_back`'s.

## What it assumes from elsewhere

- **[[linux-sim-divergence]]** owns `LinuxSimCo` and its converse. Assumed
  here: only that a `LinuxSimCo` proof is a `SimProgram` proof.

## Log

- 2026-11-06: Done by the fuelled route instead of the coinductive one (the question was put to Minus on the thread's decision card; the fuelled route kept the compiler's proofs inductive). `SimPaid` (`lib/std/os/linux/linux_x86_64_sim_paid.hthr`) is `Sim` read one constructor at a time with every `Tau` costing the machine at least one step; it is a `Sim` (`sim_of_paid`), and its converse is exact when the tree's cuts lie deeper than the run takes steps (`paid_run_whole`). `ITree::Deep` (`lib/std/itree/itree_deep.hthr`) is that depth, kept by bind and put at fuel `n` by every loop (`deep_iter`); a source's cuts lie as deep as its fuel (`Source::deepens`). The compiler's `Site::Goes` now claims `SimPaid`, and a loop's `JMP` back pays its `Tau` (`goes_jmp_tau`, `Target::at_jmp_tau`). `Source::elf_runs_exact`: every run of the process `write-elf` describes, with answers Linux may give, is the events of a whole trace the source produces; a source that never returns compiles to a process with no run (probe `spin_paid_no_run`). `elf_simulates`/`elf_file_simulates` keep their `SimProgram` statements through `Program::sim_of_paid`, so the certificate is unchanged. `LinuxSimCo` stays as the coinductive statement over `Source::tree_co`; nothing needs it now.
