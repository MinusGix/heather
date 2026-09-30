---
title: tr: a certified program that writes after every chunk
status: open
labels: [x86,native,program]
created: 2026-09-30
updated: 2026-09-30
---

The third real program after `wc -l` and `wc` ([[native-wc]]): `tr a-z A-Z`
as a certified static executable. It breaks the read-everything-then-write
template twice. It writes inside the read loop, so read and write histories
interleave. And it stores a byte for every byte it reads, translating each
chunk in place before writing it back. Its claim has no bound on the input.

Design: `docs/native-tr-design.md`. The byte map is lowered through the
compiler (needs [[function-ir-narrow-arithmetic]]'s add/subtract, slice N);
the map loop and the process are library code proved once. `tr -d` and
`tr -s` are [[native-loop-emitting-stores]].

## Log
