---
title: Let compiled programs' region addresses evaluate past the kernel's depth limit
status: closed
labels: [native,x86,kernel,performance]
area: heather-in-heather
milestone: [hih-pl-first-program]
created: 2026-10-25
updated: 2026-10-26
---

`native_compile` spells every address in its region as `next_rip(low,
offset)` (`Layout::word_at`, `buffer_at`, `scratch_at`), and `next_rip` is
`iterate_increment`: `offset` increments, each matching on the one before.
Evaluating such an address's bits re-enters the kernel's evaluator once per
increment (docs/native-depth-budget-design.md §1), so at an offset of about
1024 (`NATIVE_DEPTH_LIMIT`) it is `OutOfFuel` before any fuel is spent, and
below that each address costs a large share of a declaration's fuel (an
offset of 768: ~100k steps for its eight bytes; 400: ~50k).

Nothing in `native_compile_correct` evaluates an address, so the theorem
holds at any layout. What does is anything that reads the program's bytes:
`heather write-elf` (issues/native-cat-executable.md) checks the file by
evaluation, and cat's scratch range at `cat(1024)` is 512 + 1024 bytes past
the page. So cat is compiled at 256 (`cat_capacity`), and any source whose
words, buffers and scratch range pass ~1000 bytes cannot be written.

## Routes

- Spell region addresses with a ripple adder (`low.add(BitVec::ofNat(o))`,
  depth bounded by the width) and restate the region lemmas over it; the
  layout proofs that want `next_rip`'s composition shape would need the
  bridge `iterate_increment_toNat` already gives.
- Or a kernel fast path for `iterate_increment` on a closed word and a
  numeral (the native bit-vector values,
  issues/kernel-native-bitvector-values.md), which also takes the per-address
  cost out of `write-elf`'s byte pieces.

Found 2026-10-25 writing cat's executable.

## Log

- 2026-10-26: Fixed by the first route. `BitVec::add_nat(a, o)` (bitvec.hthr) is `a.add(BitVec::ofNat(o))`, a ripple add whose bits evaluate in frames bounded by the width, and `BitVec::add_nat_iterate` proves it `a.iterate_increment(o)` below the period. `Layout::word_at`/`buffer_at`/`scratch_at` now spell their addresses with it; the region lemmas stay over `next_rip`, and `Target::at_rip` (with `word_rip`, `buffer_rip`, `scratch_rip`) carries a statement across in the six places that leaned on the two being one term (read_slot, placed_word, goes_word_from, buffer_toNat, landed_store/landed_word, goes_read_back_ok's loop entry, goes_reads). `write-elf`'s literal spells region addresses `add_nat` too, so the emission check still compares by arguments. `cat_capacity()` is 1024: all of lib/native checks, and `write-elf` writes cat with its scratch range at offset 1536 (0x410600), which copies 5000 random bytes intact and exits 1 on a full stdout. Not done: `PIECE` in elf.rs is still 48 bytes, sized for `next_rip` addresses; it could likely grow now.
