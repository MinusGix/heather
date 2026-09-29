---
title: Two loop generators where a Nat carry could be a one-field record
status: open
labels: [native, generator, simplification]
code: crates/elab/src/function_ir_source/loop_record.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

`generate_elaborated_loop_x86` (Nat or Bool carry, with its own placement of
13 registers) and `generate_elaborated_record_loop_x86` (record carry,
fields updated in place) now feed the same process, elf64_read_state
(docs/native-wc-design.md §9). The Nat generator's certificate is the record
one's shape at `rep = loop_in(R13, loop_nat_rep)`, and a Nat count is the
record case with one field.

Folding the scalar case into the record generator (a field accessor that is
the identity) would leave one loop generator, one placement type and one set
of process facts; the Nat-state lemmas in elf64_read_state (`count_framed`,
`count_room`, …) would become the record generator's emitted `_rep_moves`
and `_room`. Cost to check first: the Nat loop's code size and cold
certificate cost under the record lowering.
