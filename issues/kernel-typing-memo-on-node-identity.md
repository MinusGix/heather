---
title: Memoize kernel typing on node identity, so a shared let value is checked once
status: open
labels: [kernel,performance,proofs]
area: kernel
created: 2026-09-25
updated: 2026-10-26
---

The kernel re-checks a shared subterm once per path to it: `Tc::tm_infer` and
`tm_check` (crates/kernel/src/typing.rs) keep no memo keyed on node identity.
A transparent `let` chain in which each let uses the previous one twice
therefore costs 2^k in the gate, and at k = 16 a correct proof is rejected
with `OutOfFuel` ([[proof-let-substitution-cost]]'s `dep` family). `have`
(docs/have-design.md) fixes the opaque case. This issue is the case where a
later proof needs the value, such as a state `s1 = w.after` that proofs about
`s1` must see through.

## Design constraints (from the 2026-09-25 discussion)

- **Determinism.** A hit must not charge fuel, or it saves nothing, since
  fuel is what rejects `dep_16`. So which lookups hit must not depend on
  memory addresses. That rules out a direct-mapped cache that evicts by
  address (the `bounds.rs` shape), and it rules out filtering on
  `Rc::strong_count` (the bounds cache's keep-alive entries perturb it).
  What fits: an unbounded map per gate item, dropped when the item ends. Each
  entry holds its `Rc`, so the address cannot be reused mid-item, and entries
  are chosen by node kind (application and projection nodes), never by
  collision. Timings counts must stay exact and independent of the worker
  count.
- **Key.** Node address, local-context identity (the shared-spine test
  `CtxEntries` already makes O(1)), layer and universe count. Memoize
  inference, and memoize check-mode successes keyed also on the expected
  type's address. Arguments are often checked, not inferred (`refl`, `λ`).
  Failures are never memoized.
- **Trusted base.** The memo is kernel state; a wrong key is a soundness bug.
  Debug builds should re-run the real check behind a sample of hits, the way
  `bounds.rs`'s skips are re-verified.
- **Reach.** Only aliases that arrive unshifted share. A use under a binder
  is a fresh `shift_local` copy, and `map_term` has no per-traversal memo, so
  the print proof's `λ rcx r11 => { … }` continuation would still pay. A
  per-traversal memo in the shift, applied only to shared nodes, is a
  separate small change in `subst.rs`. Name it in the same round or file it.

## Acceptance

- `dep` at growing k (the synthetic family in the anchor issue's log) is
  linear in gate queries, and `dep_16` checks.
- `scripts/bench --check` shows no regression on one-shot checking
  (`code/check-identity-recursor` is the known sensitive row;
  [[bounds-metadata-taxes-one-shot-checking]]).
- `--timings` counts are identical at widths 1 and 8.

## What it assumes from elsewhere

- **[[proof-let-substitution-cost]]** owns the diagnosis and the
  measurements. Assumed here: only that the gate is where transparent
  fan-out pays.
- **[[conjunction-projection-chain-cost]]**: likely a second customer (the
  shared receiver re-inferred per projection).

## Log

- 2026-10-26: mengine (a λ-DAG proof engine, docs/mengine-survey.md §3.1) types every node at construction and stores the type, so a proof costs its distinct nodes: this issue's property across a whole engine. Two transferable details: it caches an application's type by the pair of child pointers (`g_app_type_cache`), so separately built `f a` nodes with shared children share the work; and it has no fuel, which is why it never meets this issue's determinism constraint, and why it offers no help with it. The shift residue named under Reach is filed as [[subst-shared-node-memo]]; the 2026-10-26 probe (survey §4.2) shows a let-shared statement at 2^k gate queries and [[tactic-scaling-bench-families]] asks for it as a bench family.
- 2026-10-26: Reach (shift residue) resolved by [[subst-shared-node-memo]]: every pure substitution traversal memoizes shared nodes per call, and an alias is shifted once per depth, so a let alias used under a binder now reaches the gate as a shared node. The gate's own per-path walk is unchanged (the 2^k queries of the fan-under-λ probe stand), which is this issue.
