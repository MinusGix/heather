---
title: refl on two closed Nats in the thousands exceeds the depth budget where leb does not
status: open
labels: [kernel,conversion,x86,performance]
created: 2026-09-25
updated: 2026-09-25
---

`refl` cannot prove `232 + code.len() = elf_size16(lo, hi)` for a 2.7 KB
program. The kernel compares the two Nat values successor by successor on the
native stack, runs past the 1024-frame depth budget, and reports `OutOfFuel`.
`Nat::leb_sound(…, trivial)` in both directions, then `Nat::le_antisym`,
proves the same equality within budget. The generator does that now
(`crates/cli/src/native/read_loop.rs`, `{prefix}_image`, 2026-09-25). The same
file's 2757-byte list equality `_file_correct` passes by `refl`, so the list
walk is fine and the Nat comparison is not.

This is a cliff every larger program meets at every size fact, and the
error names fuel, not depth. Small step counts in `--timings` are the tell.

## Questions

- Which comparison nests? It is probably conversion of two `Succ` spines
  whose predecessors are lazily unrolled arithmetic (`+`, `len`, `elf_size16`'s
  `lo + 256*hi`), each forced in a non-tail position. Trace `Conv::tm` depth,
  the method in [[utf8-decode-conversion-blowup]]'s log.
- Why does `leb` stay within budget? If it reduces tail-recursively on the
  trampoline, conversion of two closed Nats could decide equality the same
  way, by evaluating both sides to a numeral (or a run, per
  [[succinct-inductive-values]]) first and comparing the results.
- Is the fix in conversion, in the evaluator's closed Nat arithmetic, or in
  a tail form of `Eq` on Nat? The kernel stays un-fancy: the fix must be an
  algorithm change with the same verdicts, not a bigger budget.

## Acceptance

- `refl` proves `232 + L = f(…)` for closed `L` in the tens of thousands,
  with the depth budget unchanged, and the generator's `le_antisym` detour is
  removed.
- A kernel test at a length past 1024 that would have been refused before.
