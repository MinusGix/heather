---
title: Second pass on what a write-elf certificate costs as the code grows
status: closed
labels: [native,elaboration,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-31
updated: 2026-10-31
---

Follows [[native-certificate-literal-cost]] (`cat_files_tool` 86 → 65 s).
The question for this round: of what a tool's certificate costs, what
grows with its code, so that the larger tools of the `hih-tools` list
stay cheap to certify.

## How it was measured

Cloud box, dev-profile `heather`, width one, `write-elf --timings` over a
fresh copy of a warmed store (the library replayed), families summed by
item name with digits folded (`at_#`, `e_#`, …). Code size was varied with
scratch tools of 8, 16, 24 and 32 cat passes over one file, so the same
instructions repeat and each family's per-item cost can be read off.
The before and after binaries were run one after the other on the same
box; seconds are single samples, the step counts exact.

## What grows, before this round

Every family is linear in the code (per-item steps flat from ×8 to ×32),
so what grows is each family's constant. Ranked by seconds at ×32:

| family | what it is | share of the item time |
|---|---|---|
| `at_#` | the program literal's prefixes, gated as `Prog` values | a fifth |
| `bytes_#_#` | the fork re-emitting each part to read its bytes | a sixth |
| `e_#` | each part's emission by `refl` | an eighth |
| `piece_#_is` | the assembler run per code piece | under a tenth |
| `checked_#`, `ck_#`, `read_#_part`, `upto_#_is` | the per-part checks and reads | each about a twentieth |

`at_#` was the surprise. In the kernel its steps were small, and its time
was split between the gate converting large terms and the elaborator
respelling. The terms were large because `Asm` and `Prog` had no type
codes at all: every one of their codes after the first was refused by
the kernel, because their lowering
mentions a function (`Asm`'s `measured: bytes.len() = len`) and the
codes were registered in a stale scope. Filed and fixed as
[[codes-registered-in-a-stale-scope]].

## Result

Same box, before → after (seconds, single samples):

| run | before | after |
|---|---|---|
| `cat_files_tool` write-elf | 58 s | 48 s |
| its certificate's kernel gate | 14 s | 9 s |
| 32-pass cat write-elf | 78 s | 62 s |
| its certificate's kernel gate | 19 s | 10 s |

By family on the 32-pass cat: `at_#` fell to about a third, `upto_#_is`
to under half, `e_#` and `checked_#` by about a quarter. On `cat_files_tool`
the cut is smaller (`at_#` to under half), so the gain widens with the code.

(The `cat_files_tool` figure is lower than the 65 s
[[native-certificate-literal-cost]] closed on: that was another
session's measurement on another box. The two columns here
are paired.)

## Left, largest first (32-pass cat, after)

- `bytes_#_#`, now the largest family: the fork re-emits each part to read
  its bytes; its steps grow with the parts and it has no kernel time, so
  this is the reducer, not the gate. [[native-certificate-fork-byte-reads]].
- `e_#` and `piece_#_is`, kernel `refl`s over the encoder: the
  closed-bitvector line ([[kernel-native-bitvector-values]],
  [[bitvector-literal-entry-cost]]).
- `ck_#`, `checked_#`, `read_#_part`: per part, each a small constant.
- `live_sets` and `allocation`, two items whose steps grow with the whole
  program, not per part: the first family here that is not linear in the
  code if a tool's functions grow too. Worth watching as tools get larger.
- The fixed floor of a write-elf process ([[native-process-fixed-cost]]).
