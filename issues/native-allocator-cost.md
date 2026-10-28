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

The trusted side has a cost of its own. The certificate checks the homes
with one `refl` (`{p}_allocated`), which is its largest single item at eight
times cat. Splitting it the way emission is split, one statement's
`Stmt::checked` at a time and joined like the parts, would keep each piece
small.

## Scope

- The heuristic in Rust (`crates/cli/src/native/`) emitting the same
  `Homes` spelling, if the fork's cost matters.
- The allocation check stated by parts in the certificate.
- Better choices while there: spill cost by loop depth beyond the flat ×8,
  and loop-set words coloured first.
