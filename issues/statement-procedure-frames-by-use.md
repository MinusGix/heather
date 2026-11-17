---
title: Size each statement procedure's activation by what it keeps and uses
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-16
updated: 2026-11-17
---

Each activation of a statement procedure (`native_compile.hthr`, `Procedure::entry_code`) pushes the registers it keeps and opens a frame of the layout's words, and the program's stack bound charges every level `8 * (words + 7)` (`Target::roomy`, the `deep` premise of `Source::elf_file_simulates`): six saved registers and the return address, whether the procedure keeps them or not, and the whole program's word count for every procedure. This is the statement compiler's form of [[function-frame-sized-by-use]], which sized the function lowering's frames.

What it needs: a per-procedure frame (its own words and the registers it keeps), the depth bound summed from those instead of a uniform `room * (8 * (words + 7))`, and the certificates' `deep` premise stated from the new bound.

## Closed

Built as `docs/native/native-procedure-frames-design.md` steps F1, F2 and F4 (§6 there is the as-built record): each procedure is compiled under its own frame and homes (`Frame`, `Layout::body`), saves only the callee-saved registers it does not pin, and the `deep` premise is `Source::need(homes, bodies) <= stack`, each level the callee's own `Frame::level` along the calls a body makes. Slots by index (F3) and the functions' room under the planned table (F5, `room-table-loose-ends`) are that note's remaining steps.
