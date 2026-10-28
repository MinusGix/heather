---
title: Read a word from its home register without the trip through RBX
status: open
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

`Prog::word_to` (`lib/native/native_compile.hthr`) copies a home register
into its target through RBX: two moves, kept so RBX is written on every path
and the leaf lemmas stay as they were. A direct move saves one; an S4 leaf
whose inputs are already in home registers could read them where they are
and save both, if S4's placement accepts a register it must not write.

## Scope

- `word_to` as one move for a register home, with `Held` and the leaf
  lemmas updated for RBX not being written.
- S4 leaf inputs placed in their home registers when the leaf does not
  write them.
- Sizes for cat, tr, yes and echo after.
