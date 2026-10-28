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
§6). It is quadratic in the number of words times the number of writes
(interference by scanning the write list). The heuristic is untrusted, so it
could run in Rust over the read-back source at no cost in trust.

## Scope

- Either an interference matrix built once in Heather, or the heuristic in
  Rust (`crates/cli/src/native/`) emitting the same `Homes` spelling.
- Better choices while there: spill cost by loop depth beyond the flat ×8,
  and loop-set words coloured first.
