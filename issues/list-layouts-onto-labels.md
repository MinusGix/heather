---
title: Move the last list layouts onto x86_64_asm labels
status: closed
labels: [native,x86,proofs]
area: heather-in-heather
created: 2026-10-20
updated: 2026-10-21
---

The list layouts (`x86_64_layout`'s `layout_code`/`layout_at`/
`layout_resident`/`LayoutMeasured`) still place the write loop
(`lib/elf64_write_loop.hthr`), the read head and failure tail
(`lib/elf64_read_pieces.hthr`), the count tail (`lib/elf64_count_print.hthr`,
`lib/elf64_filter_finish.hthr`) and the read filter's program around its chunk
loop (`lib/elf64_read_filter.hthr`). Everything else is an `x86_64_asm`
program. Moving these onto labels would leave one way to state where code is.

Parked, not scheduled: the layouts and their jumps are already Heather
functions (the producer evaluates them; nothing is mirrored in Rust but the
count tail's end in `crates/cli/src/native/read_filter.rs`), so the move is
uniformity only. These libraries are a small slice of the wc command
closure's cold kernel steps (the write loop and the read pieces a few percent
between them, the filter's outer layout part of its own), and the move is a
rewrite of their hand-threaded proofs: a piece's position is a left-nested
sum over a neutral placement today, which a label offset does not convert to,
so every `rip_advance` over them would be restated, best as stretches between
the system calls.

Take it up when one of these libraries is rewritten anyway, or when a
counter says they dominate. Acceptance as [[native-runs-remaining]]'s: no
more cold kernel steps per moved phase; `build-x86` of wc writes the same
bytes.

## Log

- 2026-10-21: Closed as not planned: the layer it is about was burned in B1 with the hand-proved native process stack (docs/native/native-program-logic-design.md §3.1, [[native-burn-process-stack]]); the last commit with it is 189659d (tag native-v0). The rebuild states programs as interaction trees and compiles them, so this per-program work does not come back in this form.
