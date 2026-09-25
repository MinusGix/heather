---
title: First real program: wc -l as a certified static executable
status: open
labels: [compiler,x86,elf,milestone]
created: 2026-09-24
updated: 2026-09-24
---

## Scope

The first certified program that takes input from outside: a static ELF that
reads stdin once, counts newlines with the certified counting loop, and exits
with the count as its status. The process claim: for every input the read may
return, the file has a run with trace `[ReadEvent(0, bytes), ExitEvent(wc_l(bytes) mod 256)]`,
where `wc_l` is an ordinary Heather function.

Design: `docs/native-first-program-design.md`.

## Current state

Slices 1–3 landed 2026-09-24: `wc -l` builds with `build-x86 --read-loop` and runs, and
its certificate states the process against `wc_l` (design §8). Slice 4, output to stdout, is next.

## Slices

1. Fetched steps for the emitted subset, and `access_fetched`: a structural
   `AccessCode` execution with layout and resident bytes is a fetched run.
   Every loop and branch certificate gets a loaded-image form from it.
2. The basic Linux trace (`LinuxEvent`, `LinuxRuns`: read and exit only).
   Its proper form is [[linux-syscall-trace-model]].
3. `wc -l` itself: spec, client lemma, process-shape theorem, `build-x86`
   profile, native and kernel-refusal tests.
4. Output (next): program byte stores ([[byte-memory-access-model]]'s write
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

- 2026-09-24: Probes V1–V5 held (design §7), with one amendment: the program gets its own memory view, `IoMemory`, which classifies addresses by value. Slices A–C landed (§8). A: `x86_64_fetched_code` proves `access_fetched`, so any loop or branch certificate runs fetched in a loaded image. B: the basic trace is in `linux_x86_64_io` and the memory view in `elf64_io`. C: the process theorem `elf64_read_loop::read_loop_runs`, `examples/x86-native/wc_l.hthr`, and `build-x86 --read-loop`. `wc -l` builds as a 625-byte certified executable in about 36 s and runs correctly on files and a pipe (`crates/cli/tests/native_read_loop.rs`). Six mutations of the process shape are refused (`crates/elab/tests/read_loop_process.rs`). Residency ended up proved by induction, not evaluated (§8 amendments). The exit-status slice is done; stdout output is next.
- 2026-09-24: Filed along the way: [[let-bound-proposition-diagnostic]], an odd refusal of a type-valued `let`. The fuel measurements are logged on [[call-memory-read-file-walk]].
