---
title: Substitution allocates fresh Var leaves for id(Γ) and a fresh memo table per call
status: open
labels: [kernel,performance,substitution]
area: kernel
created: 2026-11-02
updated: 2026-11-02
---

Cut substitution's per-call allocations: the identity substitution builds |Γ| fresh `Var` nodes, and every traversal grows a fresh memo table.

## Problem

- `LocalSubst::id(ctx)` (`crates/kernel/src/subst.rs` ~2263) allocates `|Γ|` new `Arc::new(Term::Var(..))` leaves, 144 bytes each. That happens every time a β-substitution is formed, `LocalSubst::id(&gamma).extended(arg)`, for example once per explicit argument in `elab/src/application.rs` ~796. There are 200 `LocalSubst::id(` call sites and 276 literal `Rc::new(Term::Var(` sites.
- Every pure `Mapper` call constructs a fresh `NodeMemo` (two `HashMap`s, `subst.rs` ~2000–2016, ~1412). It grows from empty by rehashing and is dropped with its keep-alives.

Measured with the gdb sampler (`docs/data-oriented-survey.md` §5): `id(Γ)` is in 1.3–3.7% of cold samples, and memo inserts (`subst.rs` ~406, ~511, mostly allocation and rehash) in 3.0–7.4%.

## Proposal

- **Shared leaves.** `Term::var(i)` hands out an interned `Arc<Term::Var(i)>` for `i` below a bound (e.g. 4 096); `Zero`, `TmNat` and `Type::Nat` get the same treatment. `id(Γ)` becomes `|Γ|` refcount increments. Extra sharing only helps the identity-keyed memos, and leaves are answered before any memo is consulted.
- **Reused memo tables.** A thread-local pool of `NodeMemo`s, cleared with capacity kept when a call ends.
- Not proposed: a lazy identity prefix in `LocalSubst`. The paper's `id_Γ` is fully expanded, and that would be a representation change to the substitution calculus.

## Cost and risk

Local to `subst.rs` and `term.rs`. Interned leaves shared across kernel workers mean contended atomic refcounts, so prefer per-thread intern tables (leaves stay `Send`), and measure with `scripts/perf ab` at width 8 as well as 1. Counters such as `local_subst_nodes` and `subst_memo_hits` must not move except where address-keyed memos already vary run to run.

## What it assumes from elsewhere

- **[[subst-rebuild-then-discard]]** owns the rebuild-then-drop pair. Assumed here: nothing; the two are independent.
- **[[kernel-arena-terms-frozen-prefix]]**: under arenas both allocations disappear. Assumed here: only that the arena is not imminent.
