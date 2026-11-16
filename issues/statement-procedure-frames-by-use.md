---
title: Size each statement procedure's activation by what it keeps and uses
status: open
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-16
---

Each activation of a statement procedure (`native_compile.hthr`, `Procedure::entry_code`) pushes the registers it keeps and opens a frame of the layout's words, and the program's stack bound charges every level `8 * (words + 7)` (`Target::roomy`, the `deep` premise of `Source::elf_file_simulates`): six saved registers and the return address, whether the procedure keeps them or not, and the whole program's word count for every procedure. This is the statement compiler's form of [[function-frame-sized-by-use]], which sized the function lowering's frames.

What it needs: a per-procedure frame (its own words and the registers it keeps), the depth bound summed from those instead of a uniform `room * (8 * (words + 7))`, and the certificates' `deep` premise stated from the new bound.
