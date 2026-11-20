---
title: Comparing two separately built neutral DAGs is quadratic in syntactic equality
status: open
labels: [kernel,conversion,performance]
area: kernel
code: crates/kernel/src/syntax_eq.rs @ 91339c55
created: 2026-11-20
updated: 2026-11-20
---

Found by the bench family `conv/shared-neutral-dag`
(`crates/kernel/benches/kernel/fixtures/conv.rs`): under `x : Nat`, two
separately built copies of `t₀ := x`, `tᵢ := elim_Nat(tᵢ₋₁; Nat; tᵢ₋₁; _ ih.
Succ ih)`, each sharing its `tᵢ₋₁`. Every eliminator is stuck on the
variable, so conversion compares two neutral spines n eliminations long.

`syntax_eq_nodes` grows as n² exactly (work slope 2.01, 616 nodes at 16
levels, 163 K at 256), and the time follows it (slope 1.7). The arena and
every other counter are linear.

## Cause

The neutral comparison (`Conv::tm_ne_elim_nat` → `tm_nee_c`) compares each
eliminator's closures, and when their environments agree it does so
syntactically (`SharedEq`). The `PairMemo` that makes syntactic equality
linear in a DAG is local to one top-level `==` (`syntax_eq.rs` header, by
design: addresses cannot be reused while it lives). Conversion makes one
such call per eliminator, and the closure at level i holds `tᵢ₋₁`, a DAG of
size i, so the walks sum to n².

## Options

- A memo that lives for one conversion query, threaded from `Conv` into
  the closure comparison. The keep-alive argument changes: the query's
  values hold the terms their closures point at, so the roots outlive it,
  but this needs stating.
- Compare the closures' terms by the pointer pair first and only then walk
  (already done for identical pointers; the sides here are distinct
  allocations, so it does not help this case).

## Log

- 2026-11-20: found by the new bench family; not fixed (a kernel change).
