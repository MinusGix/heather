---
title: Indexed Bind (IxBind) and footprint framing for within Wp
status: open
labels: [language,native,proofs,design]
area: heather-in-heather
milestone: [hih-pl-wp]
created: 2026-11-24
updated: 2026-11-24
---

Follow-up to [[proof-worlds-native-wp]] targeting `lib/std/os/linux/linux_x86_64_wp.hthr`
and `lib/native/native_compile_calls.hthr`.

## Motivation

Straight-line x86-64 WP proofs currently CPS-thread 10–14 ambient parameters
(`io`, `view`, `origin`, `tr`, `rip`, `holds`, `resident`, `trace_of`, `valid`,
`short`) and manually unpack/repack nested `⟨⟨⟨refl, …⟩⟩⟩` framing tuples at
every step. While ordinary `Bind<M>` supports forward state-invariant execution
(`Exec` in `lib/std/relation/exec_world.hthr`), full Hoare/WP proofs whose
precondition/postcondition index changes at each instruction (`P → Q → R`) need
an indexed bind and automatic framing of untouched registers and memory slices.

## Sketch

1. **Indexed bind (`IxBind`):** a 3-index sequencing class
   `ix_bind : M(P, Q, A) → (A → M(Q, R, B)) → M(P, R, B)` (lowering `let x <- e;`
   inside `within Wp` when `M` has `IxBind` instead of `Bind`).
2. **Environment-threaded WP carrier:** bundle ambient parameters (`io`, `view`,
   `origin`, `tr`, `resident`, `valid`) in the world carrier rather than
   repeating them on every continuation lambda.
3. **Footprint framing (`Wp::frame`):** declare each primitive step's modified
   register/memory footprint and lift `Wp(P, Q)` to `Wp(P ∧ R, Q ∧ R)` whenever
   `Disjoint(Modifies, Reads(R))` is discharged by `omega` or `evidence theorem`.



