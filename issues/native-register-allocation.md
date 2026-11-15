---
title: Keep the native compiler's words in registers, checked, with liveness
status: closed
labels: [native,x86,perf]
area: heather-in-heather
created: 2026-10-28
updated: 2026-10-28
---

Option 3 of the compiled-code shape work ([[native-compiled-code-shape]]'s
first scope item), approved by Minus 2026-10-28: liveness, an assignment
proposed by an untrusted heuristic, a checker as the only trusted part,
correctness proved once, spills as slots, moves and the calling convention
later. Design: `docs/native/native-register-allocation-design.md`.

## Scope

- Every word gets a home, its slot or a register of a pool no statement
  uses otherwise (`lib/native/native_alloc.hthr`).
- Liveness over the statement tree; loop sets supplied by the allocator and
  checked closed in one pass.
- `Source::compile(low, homes)` checks the homes (`Source::allocation_ok`)
  and `native_compile_correct` holds for every assignment that passes.
- A greedy allocator for write-elf, and the spill-everything one.
- Sizes of cat, tr, yes and echo before and after.

## Follow-ups

[[native-loop-sets-by-loop]], [[native-allocator-class]],
[[native-register-moves-and-convention]], [[native-homes-read-in-place]],
[[native-statement-clobbers]], [[native-leaf-pool-per-leaf]],
[[native-allocator-cost]]. The narrow leaf's register cap stays with
[[native-compile-wider-leaves]].

## Log

- 2026-10-28: Landed. Code bytes cat 1192→758, tr 1847→1170, yes 1011→733,
  echo 2648→1822 (design §8); the four rebuilt binaries behave as before.
  Allocation sets moved into `Homes.loops` after the in-check fixpoint ran
  cat's check past the kernel's per-declaration fuel.
- 2026-10-28: The PR suite found two allocator faults, both untrusted-side. `yes STR` was refused at its certificate: two loops test one word, and the separately grown sets, once joined, left a nested loop's set unclosed. The sets now grow together under the check's liveness (`Homes::closed`). The 8×-cat probe failed on write-elf's fork: lazily built tables nested past the evaluator's depth, which the reader reports as running out of fuel. The passes are now linear, the interference graph is flag rows, and each `put` is settled as it is made. write-elf now refuses failing homes by reason 12 before it writes the certificate. The compile tests check with slot homes, since the greedy allocator beside a compile does not fit one declaration's fuel. The four tools' sizes are unchanged.
