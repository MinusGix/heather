---
title: Prove bounded-width executable BitVec addition and subtraction
status: open
labels: [stdlib,bitvectors,proofs,performance]
created: 2026-09-07
updated: 2026-09-07
---

## Problem and scope

Large literals now construct efficiently, but bitvec::add and bitvec::sub still
iterate increment/decrement to the unsigned value of the second operand. In
particular, adding a sign-extended negative displacement can request an enormous
iteration. Supply structural arithmetic whose algorithmic work depends on bit
width, with generic proofs equating its results to the existing definitions.
This is library arithmetic work, separate from the checker's resource diagnostics.

## Acceptance

- Add structural modular add/sub operations with work bounded by width rather
  than operand magnitude, reusing existing carry/borrow machinery where useful.
  Names are provisional; keep existing add/sub definitions and their current
  definitional behavior intact for this round.
- Prove equality to existing add/sub for arbitrary width and open operands.
  If using carry/borrow inputs internally, state and prove their meaning.
  Use ordinary checked Heather proofs, with no new axioms or trusted evaluator
  shortcuts. A handful of closed examples is not a correctness proof.
- Expose congruence/transport lemmas that let a future generator replace an
  expensive concrete computation while keeping canonical arithmetic semantics.
- Exercise widths 0, 1, 8, 32, and 64; zero, all ones, modular wrap, underflow,
  the high-bit boundary, mixed bits, and full-width negative-offset patterns.
  Test open/neutral operands and include a kernel refusal control for a wrong
  result. Small-width reference comparisons may compute the old definitions;
  large tests must not force the very unsigned iteration this issue removes.
- Verify representative width-64 computations within ordinary fuel/memory/CPU
  rails. Use the repository's documented performance protocol for measurements,
  and record enough bounded evidence to distinguish width from magnitude cost.
- Run focused tests and the full scripts/test gate. Keep a resource diagnostic
  failure separate from mathematical incorrectness or an algorithmic bound.

## Independent handoff boundary

Work in the BitVec library, its focused tests, and this issue. A separate helper
module is acceptable if it reduces churn. Do not edit x86 models, call generators,
ELF files, native examples, or kernel/frontend implementation. The coordinator
will integrate the proved operations into x86 after the API is reviewed. The
uncommitted calls implementation is not a prerequisite: existing arithmetic and
carry/borrow code plus the cases above are sufficient to start from a worktree.

## What it assumes from elsewhere

- [[fixed-width-bitvectors]] owns the existing carrier and arithmetic definitions.
- [[bitvec-executable-carry-correspondence]] owns the existing carry correspondence.
- [[bitvec-executable-borrow-correspondence]] owns the borrow correspondence.
- [[bitvec-ofnat-large-literals]] supplies bounded-width literal construction.
- [[bitvec-closed-reduction-cost]] owns refusing excessive computation safely;
  this issue owns a better arithmetic algorithm, not that checker repair.
