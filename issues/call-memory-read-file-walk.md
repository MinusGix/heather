---
title: A stack-address call_memory_read walks the whole ELF file list before reaching the stack
status: open
labels: [x86,elf,stdlib,performance]
created: 2026-09-12
updated: 2026-09-12
---

Filed from the K2 design pass (docs/call-memory-read-spelling-design.md §2, 2026-09-12). `static_elf64_read` (lib/elf64_load.hthr) decides file membership by a 48-bit window test over the whole 64 KiB at 0x400000, and the owned stack page at 0x401000 lies inside that window. So a `call_memory_read` at a stack address passes the test and produces its `None` by `file.nth(i)` running off the end of the file: a unary walk of every file byte (399 here), 31.5 k evaluator steps / 179 ms per lookup, linear in the size of the compiled program. The certificate's eight most expensive theorems (`read_literal_28_*`, 188 k steps each) were six such lookups and nothing else; the fetch route already avoids it through `static_elf64_read_split`.

The round fixes the contract read route by stating the callee contract over `stack_observation` ([[function-ir-x86-proof-scaling]]), which removes the lookups from that path without changing what the file read means. What remains on this unit:

- `dead_frame_byte` (one item, 0.21 s) deliberately observes a dead frame slot through the full `call_memory_read` and pays one walk; the honest shortcut is a `list::nth` past-the-end lemma (`xs.len() ≤ i → xs.nth(i) = None`, a short induction in lib/std/list.hthr) plus a `call_memory_read` lemma keyed on it — worth ~5× on the unit (the length is 6 k steps), not 19×.
- The definition itself: a window test that admits the stack page is a spelling whose cost is proportional to the program; whether `static_elf64_read` should test the file's own length (or the segment's size from the header) before indexing is a model question — the executable-image profile in `lib/elf64_calls.hthr` says the RX file ends before the stack page (`disjoint_stack`), so a read that consults that fact is faithful. Decide when the next consumer of a full-observation stack read appears.
