---
title: Run the register allocator's heuristic cheaply
status: open
labels: [native,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Greedy::colouring` (`lib/native/native_alloc.hthr`) costs more than one
declaration's kernel fuel on cat, so write-elf evaluates it on its fork and
spells the homes as a literal (`docs/native-register-allocation-design.md`
§6). It makes a few linear liveness passes and one graph pass over flag
rows, settled as they are built so the lazy tables stay shallow. The
heuristic is untrusted, so it could run in Rust over the read-back source at
no cost in trust.

The trusted side's single `refl` (`{p}_allocated`) is gone: the
certificate states the check over the emission's parts
([[native-tool-certificate-budget]]).

## Scope

- The heuristic in Rust (`crates/cli/src/native/`) emitting the same
  `Homes` spelling, if the fork's cost matters.
- ~~The allocation check stated by parts in the certificate.~~ Done in
  [[native-tool-certificate-budget]].
- Better choices while there: spill cost by loop depth beyond the flat ×8,
  and loop-set words coloured first.

## Log

- 2026-10-28: with lowering, entry and the check stated by parts, the fork
  allocator is the wall for the next tool size. A probe of twice cat
  FILE's body in sequence runs out of memory (8 GiB rail) evaluating
  `{p}_homes_spelled`; a `wc` a little bigger than `head -n` does the same
  on master (decimal I/O thread, which takes the interference graph's cost
  in `native_alloc.hthr` next). The fork's evaluation, not the kernel, is
  what needs the cheaper heuristic now.
- 2026-10-28 (round 9, [[native-decimal-io]]): the fork's cost mattered.
  `wc [-clw]` ran write-elf out of the 8 GiB rail in `{p}_homes_spelled`
  (`head -n N`, smaller, already spent ~9M steps and ~2.9 GB there): a
  fork read keeps every value it forces, so the allocator's memory grew
  with its work, which is the program's writes times their live sets. The
  heuristic now runs in Rust (`crates/cli/src/native/allocator.rs`), the
  Heather allocator step for step over the read-back source, so it proposes
  the same homes (head -n's bytes are identical either way);
  `HEATHER_ELF_ALLOCATOR=both` runs both and refuses unless they agree, and
  `native_tools.rs` builds `tr` that way. The first scope item is done, and
  the check by parts landed with [[native-tool-certificate-budget]]; the
  better choices are what is left.
- 2026-11-05: gardener: cites a file it shares with [[native-procedures-write-elf-capacity]] (`lib/native/native_alloc.hthr`).
