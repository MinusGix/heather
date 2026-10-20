---
title: A stack-address call_memory_read walks the whole ELF file list before reaching the stack
status: open
labels: [x86,elf,stdlib,performance]
area: heather-in-heather
created: 2026-09-12
updated: 2026-09-24
---

Filed from the K2 design pass (docs/call-memory-read-spelling-design.md §2, 2026-09-12). `static_elf64_read` (lib/elf64_load.hthr) decides file membership by a 48-bit window test over the whole 64 KiB at 0x400000, and the owned stack page at 0x401000 lies inside that window. So a `call_memory_read` at a stack address passes the test and produces its `None` by `file.nth(i)` running off the end of the file: a unary walk of every file byte (399 here), 31.5 k evaluator steps / 179 ms per lookup, linear in the size of the compiled program. The certificate's eight most expensive theorems (`read_literal_28_*`, 188 k steps each) were six such lookups and nothing else; the fetch route already avoids it through `static_elf64_read_split`.

The round fixes the contract read route by stating the callee contract over `stack_observation` ([[function-ir-x86-proof-scaling]]), which removes the lookups from that path without changing what the file read means. What remains on this unit:

- `dead_frame_byte` (one item, 0.21 s) deliberately observes a dead frame slot through the full `call_memory_read` and pays one walk; the honest shortcut is a `list::nth` past-the-end lemma (`xs.len() ≤ i → xs.nth(i) = None`, a short induction in lib/std/list.hthr) plus a `call_memory_read` lemma keyed on it — worth ~5× on the unit (the length is 6 k steps), not 19×.
- The definition itself: a window test that admits the stack page is a spelling whose cost is proportional to the program; whether `static_elf64_read` should test the file's own length (or the segment's size from the header) before indexing is a model question — the executable-image profile in `lib/elf64_calls.hthr` says the RX file ends before the stack page (`disjoint_stack`), so a read that consults that fact is faithful. Decide when the next consumer of a full-observation stack read appears.

## Log

- 2026-09-13: 2026-09-13: after K2 the certificate's file walks are two items: dead_frame_byte (0.23 s, 52 k steps) and file_correct (0.34 s, 145 k steps, the whole-file equation by refl); read_literal is 0.58 s over 32 items. The nth past-the-end shortcut is being probed this session.
- 2026-09-13: 2026-09-13 the dead_frame_byte shortcut was built and measured (release, W=1, same box, before/after): nth_past_end (lib/std/list.hthr, landed) plus static_elf64_read_past_end (page test, offset, file.len() <= index by computation) and call_stack_read routing the generated theorem through them. Kernel 0.231 → 0.152 s and the item's steps rose 52 k → 75 k, but the item total rose 0.235 → 0.274 s: the elaborator's own whnf (elab_whnf 0.116 s) normalizes the length hypothesis to see that 'trivial' fits, so the file walk moved from the kernel to the elaborator and was paid twice. Not landed; the two elf-side lemmas and the generator route are in the session's scratchpad. The shortcut only pays once the length fact is a named theorem checked once, or the definition consults the length — the model question above.
- 2026-09-24: Measured while building `docs/native-first-program-design.md` (width one, `--timings`). One `static_elf64_read` at a literal address costs about 20K evaluator steps, most of it bit slicing (`drop_low`, `is_zero_bits`, `take_low`). An `nth` into a byte chain costs about 65 steps per element walked. So an evaluated check over every byte of a program ran out of the 2^20 per-declaration fuel at about 40 bytes. The read-once profile avoids both costs: `elf64_io` reads the file by value (`io_file_read`) and proves residency by induction (`io_suffix_resident`), with nothing evaluated per byte. The same route may suit the call profile's per-byte fetch evidence.
