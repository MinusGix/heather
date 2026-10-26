---
title: Let compiled programs' region addresses evaluate past the kernel's depth limit
status: open
labels: [native,x86,kernel,performance]
area: heather-in-heather
milestone: [hih-pl-first-program]
created: 2026-10-25
updated: 2026-10-25
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
