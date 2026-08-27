---
title: Emit compact block-level certificates for additive normalization
status: closed
labels: [proofs,elaboration,metaprogramming,performance,stdlib]
created: 2026-08-26
updated: 2026-08-26
---

The additive `arith` fragment decides its current grammar cheaply in Rust, but
its first proof plan normalized both sides to right-associated atom lists,
moved atoms through repeated adjacent swaps, and joined every step with
explicit transitivity and congruence. The kernel cost is therefore certificate
shape, not arithmetic evaluation.

Component measurements on the carry-shaped equality made the distribution
concrete. Before a compact swap lemma, permutation alone cost 28,220 term
closures, reassociation 14,261, and `twice_add` only 155. Adding the ordinary
proved `nat::add_left_comm` lemma reduced permutation to 9,529 and the full
certificate from 62,886 closures (4.1 times handwritten) to 41,353 (2.7
times). The remaining gap is dominated by reassociation and by composing the
left normalization, permutation, and reversed right normalization chains.

Design a block-level proof plan rather than adding carry-specific templates.
Promising directions include recognizing larger moves supported by
`add_swap_middle`, preserving useful source grouping, cancelling common proof
prefixes/suffixes, and producing balanced rather than linear transitivity
trees. A small additional standard monoid lemma is appropriate when it is
independently useful and proved in Heather; a kernel arithmetic primitive or a
Rust-trusted equality verdict is not.

Acceptance:

- The current five-atom carry-shaped certificate is materially closer to its
  15,337-closure handwritten comparison than the present 41,353, with new
  absolute and relative metric rails and zero eviction.
- A family of larger open additive permutations records certificate growth so
  an apparently local improvement cannot hide quadratic or worse scaling.
- Opaque atoms and coefficient-preserving `twice` behavior remain unchanged;
  expansion is still a deliberate fallback, never eager reduction.
- Audit reports expose the high-level transformation plan and exact lemma set,
  not only a count of adjacent swaps.
- Unequal coefficients and mutated goals remain rejected by the final kernel
  gate, with the existing structured normal-form diagnostic.
- Representative generation/elaboration time and final-gate time are measured
  separately; deterministic closure counts, not noisy milliseconds, are the
  regression assertions.

## What it assumes from elsewhere

- **[[certifying-arithmetic-proof-automation]]** owns the fragment boundary,
  checking-only trust story, and public audit/failure interface. This issue
  owns certificate planning and size.
- **[[perf-tracking-consistent-environment]]** owns any future stable
  wall-clock regression environment. Until then, time measurements are
  diagnostic and event counts are the rails.

## Log

- 2026-08-26: Filed after component profiling showed that `twice` distribution
  is negligible and that permutation/reassociation proof structure consumes
  nearly all checking work. `nat::add_left_comm` demonstrated that naming one
  general, kernel-proved block transformation can remove tens of thousands of
  evaluator closures without widening the trusted boundary.
- 2026-08-26: Superseded without implementation: the specialized arith normalizer was deleted after Omega gained impossible-constant reconstruction and preserved its affine Nat identity coverage. Finite branching moved to split_all/all_goals, while the bitvector twice proof remains explicit. There is no longer an additive certificate generator for this issue to optimize.
