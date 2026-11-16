---
title: First real program: wc -l as a certified static executable
status: closed
labels: [compiler,x86,elf,milestone]
created: 2026-09-24
updated: 2026-09-25
---

## Scope

The first certified program that takes input from outside: a static ELF that
reads stdin once, counts newlines with the certified counting loop, and exits
with the count as its status. The process claim: for every input the read may
return, the file has a run with trace `[ReadEvent(0, bytes), ExitEvent(wc_l(bytes) mod 256)]`,
where `wc_l` is an ordinary Heather function.

Design: `docs/archive/native-first-program-design.md`.

## Current state

Done (closed 2026-09-25). Slices 1–4 landed. `wc -l` builds with
`build-x86 --read-loop`, exits with its count, and its certificate states the
process against `wc_l` (design §8). `--print --bound <theorem>` makes it print
the count instead and exit 0, with the certificate stating the write (§10).
Both profiles' process shapes have kernel-refusal tests
(`crates/elab/tests/read_loop_process.rs`, `read_print_process.rs`). The fixed 4096-byte read, one RW
page, is [[linux-syscall-trace-model]]'s: a read loop until end of input makes
the input size independent of the buffer, so it is not made an argument here.

## Slices

1. Fetched steps for the emitted subset, and `access_fetched`: a structural
   `AccessCode` execution with layout and resident bytes is a fetched run.
   Every loop and branch certificate gets a loaded-image form from it.
2. The basic Linux trace (`LinuxEvent`, `LinuxRuns`: read and exit only).
   Its proper form is [[linux-syscall-trace-model]].
3. `wc -l` itself: spec, client lemma, process-shape theorem, `build-x86`
   profile, native and kernel-refusal tests.
4. Output (landed 2026-09-25): program byte stores ([[byte-memory-access-model]]'s write
   subset), decimal formatting as a writing loop, a write event.

## Acceptance

- The claim above kernel-checks for the built file, open in the input bytes.
- The loop certificate is the existing counting certificate, unchanged; its
  fetched form comes from the library bridge, not generated fetch evidence.
- The process shape is a library theorem with no `wc -l`-specific machinery.
- Native runs match a reference over files and pipes. Kernel refusals cover a
  wrong buffer, an oversized read cap, a wrong syscall number, and a spec that
  counts another byte.

## What it assumes from elsewhere

- [[native-bounded-loop-certificates]] (closed) supplies the loop.
- [[x86-64-machine-model]]: `FetchedStep` is the first slice of its canonical
  step, restricted to emitted forms.
- [[x86-static-elf-executable]] and the call profile supply the image and the
  RW page used as the buffer.

## Log

- 2026-09-24: Probes V1–V5 held (design §7), with one amendment: the program gets its own memory view, `IoMemory`, which classifies addresses by value. Slices A–C landed (§8). A: `x86_64_fetched_code` proves `access_fetched`, so any loop or branch certificate runs fetched in a loaded image. B: the basic trace is in `linux_x86_64_io` and the memory view in `elf64_io`. C: the process theorem `elf64_read_loop::read_loop_runs`, `examples/x86-native/wc_l.hthr`, and `build-x86 --read-loop`. `wc -l` builds as a 625-byte certified executable in about 36 s and runs correctly on files and a pipe (`crates/cli/tests/native_read_loop.rs`). Six mutations of the process shape are refused (`crates/elab/tests/read_loop_process.rs`, `read_print_process.rs`). Residency ended up proved by induction, not evaluated (§8 amendments). The exit-status slice is done; stdout output is next.
- 2026-09-24: Filed along the way: [[let-bound-proposition-diagnostic]], an odd refusal of a type-valued `let`. The fuel measurements are logged on [[call-memory-read-file-walk]].
- 2026-09-25: Slice 4 started. Its compiler part landed: word-valued helpers compose, and composed certificates cross at the helper call, so a 16-link decimal formatter certifies (1562 bytes, about 35 s) and agrees with C on every n below 10 000. Four generator fixes, attributed per item: design §10.1. Residues: a link still costs about 40K steps more per level (quadratic in depth, within fuel at 16), and valuation lookups peel the id at about 1.3K steps a level ([[valuation-lookup-case-step-cost]]). Remaining pieces: §10.2.
- 2026-09-25: Slice 4 landed (design §10.2–§10.3). The new library modules are `x86_64_store` (word store), `decimal_line` (formatter source functions and their meaning below 10 000), and `elf64_read_print` (process theorem `read_print_runs`). `linux_x86_64_io` gains `WriteEvent`, and `LinuxRuns` now runs over `FetchedStep ∨ StoreStep`. The CLI flags are `--print --bound`, and `wc_l_bounded` is in the example. The built file is 2757 bytes and matches `wc -l` on every input width, a pipe included (`crates/cli/tests/native_read_loop.rs`). Scaling it into budget took three general lessons, recorded in design §10.3: `let` chains, projection chains, and `refl` on large Nats. A fresh print build sits close to the test process's CPU rail. Filed along the way: [[omega-respells-atoms-without-implicits]].
- 2026-09-25: Follow-ups filed from slice 4. Speed: [[nat-div-mod-lemma-kit]], [[omega-div-mod-goal-cost]], [[proof-let-substitution-cost]], [[conjunction-projection-chain-cost]], [[closed-nat-equality-depth-budget]], [[crossing-link-quadratic-cost]]. Test rail: [[native-print-test-cpu-margin]]. Generator API: [[generator-name-scope-follows-last-module]]. Automation: [[bitvec-nat-lifting-tactic]].
- 2026-09-25: Closed. The print profile's refusal test is `slow_acceptance_read_print_refusals` in `crates/elab/tests/read_print_process.rs`, a process of its own because beside `read_loop_process`'s tests it passed the CPU rail. It rejects seven one-token changes: the write syscall, the descriptor, the swapped write registers, a store off the page, the stored register, and a nonzero exit. The fixed 4096-byte read goes to [[linux-syscall-trace-model]]. The print test's margin stays with [[native-print-test-cpu-margin]].
