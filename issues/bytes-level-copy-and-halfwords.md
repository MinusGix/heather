---
title: The bytes level's typed copy and two-byte accesses lowered
status: open
labels: [native,x86,memory]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Two node forms `lib/native/bytes_level/bytes_level_lower.hthr` refuses: the typed copy (`Instr::Copy`; a byte loop or `REP MOVSB`, its injection lemma the general put of a piece, [[contract-put-of-a-piece-injected]]), and two-byte loads and stores (the machine model has no `MOVZX r, word [base]` nor `MOV word [base], r16`; adding them to `x86_64` with their `Site::moves_*` lemmas is the change). The deleted experiment's probe "a typed copy of a record holding a reference lowers to the same MOVs as a word copy" waits for the first.

## Done when

`Instr::emit` lowers both, `Instr::emit_emits` covers them, and a probe copies a record holding a reference.
