---
title: refl on two closed Nats in the thousands exceeds the depth budget where leb does not
status: closed
labels: [kernel,conversion,x86,performance]
created: 2026-09-25
updated: 2026-09-28
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

## Log

- 2026-09-28: Fixed Nat conversion's recursive prefix walk. Ordinary `Succ/Succ` and
  `Values::cancel_nat_prefix` both re-entered `tm` through `tm_at_nat`, retaining
  one native depth slot per residual pair. Compression only cancels exposed
  heads; delayed successors and segmented runs still met the 1024 limit, and
  `Eval::reserve_depth` inherited conversion's accumulated depth.

  `TmProgress` now returns completed comparisons or residual Nat pairs from
  `tm_nf`/`tm_w`. Both `tm` and `tm_root` drive residuals through `tm_nat_tail`,
  which holds one depth slot and preserves entry fuel, scoped identity/memo
  checks, WHNF, delta-lazy comparison and transport stripping. Pending memo
  keys receive only a completed equality/inequality verdict; exhaustion stores
  no unfinished verdict and restores depth. Evaluator rules, equality rules,
  `NATIVE_DEPTH_LIMIT` and `DEFAULT_FUEL` are unchanged.

  The reviewed candidate's kernel approach was adopted and its stale generator
  patch adapted. The ELF size fact now uses `refl`; the remaining `closed_eq`
  helper was removed and its eight read/write jump facts also use `refl`.
  Independent inequality proofs retain `leb_sound`.

  Pre-fix candidate regressions: 1 passed, 5 failed with `OutOfFuel`, including
  1025 delayed successors and segmented runs. Post-fix kernel package: 416
  passed before adding a seventh regression for residual memo hits and nonzero
  caller depth. The final full run passes all 111 kernel unit tests (all seven
  new regressions), including chains through 50000 successors, mixed runs,
  open tails, off-by-one rejection, fuel retry, and the unchanged depth guard.
  An end-to-end `refl` proves `232 + List::replicate(0, 20000).len() = 8 + 256*79`,
  also at an open element type, and rejects wrong/neutral size facts. Restoring
  only old `conv.rs` makes that same theorem fail with kernel `OutOfFuel`.

  Final source verification used plain `scripts/test` (four bounded jobs):
  INCOMPLETE (3045 passed before death, 0 failed). All four native read/print
  checks pass, including a certificate-wide no-antisym assertion, execution
  and syscall failure cases; the print process's mutation controls pass too.
  The incomplete read-loop process group hits its unchanged CPU rail on the
  old conversion source as well. Its mutation test also exceeds the rail alone.
  That separate baseline limitation belongs to [[read-loop-process-test-cpu-rail]];
  a prefix-sharing fixture experiment did not solve it and was reverted.
  No test rail, skip list or fixture implementation changed.

  The nested-append 32768-element candidate fixture exhausted ordinary fuel
  at depth 3 after the fix; the linear 20000-element fixture meets acceptance
  within default fuel. Large computations can still exhaust step fuel and
  truly nested evaluation can still exhaust depth. The Nat issue's acceptance
  is met; a green whole-suite verdict is still blocked by the separate test rail.
