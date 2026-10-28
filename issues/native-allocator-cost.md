---
title: Run the register allocator's heuristic cheaply
status: open
labels: [native,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Allocator::greedy` (`lib/native/native_alloc.hthr`) costs more than one
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
