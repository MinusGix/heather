---
title: Stop re-matching the same type instances at every constructor of a literal
status: open
labels: [elaboration,performance,native]
area: language
milestone: [hih-tools]
created: 2026-10-27
updated: 2026-10-27
---

Split from [[write-elf-build-constants]]. Elaborating a `Prog` literal
(`At(At(…, 0, Syscall), …)`, write-elf's `{p}_at_k`) runs `instance_match`
(`crates/elab/src/gendefs.rs`, the per-instantiation type codes'
hole-match) about ten times per `At`, plus about four per `Block([…])`
item, and declines `respell_ty_at Asm no-closed-code` about forty times per
`At`. Each match succeeds; nothing about the literal changes between one
`At` and the next, so these are the same questions asked again.

Attributed on a probe of 32 `At(…, 0, Syscall)` (cloud box, a
value-metrics build, the declines by `HEATHER_GENDEF_DECLINES=1`, the
matches by a temporary per-call trace): almost all of the time is `List`
matches (about six per `At`, each well under a millisecond but the largest
per-call cost of any instance the library matches), the `BitVec` ones are
cheap. A one-`At` literal costs about 66 matches and `Start` alone 39, so
there is a per-declaration constant too. In write-elf's certificate the
literal is now the largest family left (cat_x8: `at_k` 30 s of a 104 s
build at width one, `instance_match_ns` over half of it).

## Directions

- Find which elaboration step respells the constructor's field types (the
  lowered `Asm` is a sum whose `Code`/`Proved`/`Piece`/`Refer` fields carry
  `List<BitVec(8)>`) at every application, and whether it needs to: a
  constructor applied in a checking position against its own declared type
  has nothing to respell.
- Otherwise memoize the match per (declaration, subject type, depth,
  scratch) within a declaration, keeping the subject alive with the memo so
  a pointer key cannot be reused.

## Done when

A literal's `instance_match_calls` no longer grows with its constructor
count, or what grows is attributed and justified.
