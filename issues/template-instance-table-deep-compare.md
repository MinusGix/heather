---
title: The type-code template instance table compares arguments structurally on every lookup
status: open
labels: [performance,elab,inductive]
area: language
created: 2026-11-18
updated: 2026-11-18
code: crates/elab/src/gendefs.rs:1016 @ 392affe4
---

Found by [[elaboration-cost-overview-2026-11-18]]. `instance_of_template` (`gendefs.rs`) keeps the instances of a per-instantiation type code (`docs/inductives/per-instantiation-type-codes-design.md` §4.2) by the template's address and `args_shape`, a hash of the arguments' first `SHAPE_NODES` nodes. A lookup then scans the bucket and compares each entry's arguments with `==`: a full structural walk, since equal arguments are "seldom the same nodes" (its own doc comment).

`x86_64::decode_opcode_reference` (13 s cold, the library's fifth heaviest declaration) is a chain of nested `match opcode.eq_dec(k)` arms returning `ByteDecode(bytes)` values. Measured 2026-11-18 with `--only`: **62,469 lookups, 94% of them hits, cost 231 M of the declaration's 252 M syntax-equality nodes** (about 3,700 per lookup). Buckets held up to 52 entries, so a lookup also compares against many instances that share the shape and differ deeper.

## What would fix it

Key the table by a full structural hash of the arguments, computed once per lookup, so a miss costs one hash and a hit one comparison. Better, intern equal arguments, so that a hit is a pointer comparison and the instances downstream share nodes too.

## Benchmarks

The probe case `x86/decode-opcode-reference` (`scripts/bench-probes`); its `eq` column is the one that should fall. A synthetic chain of `eq_dec` arms over a small indexed record did not reproduce it (2026-11-18): the arguments have to be large. A fixture that does is still wanted.
