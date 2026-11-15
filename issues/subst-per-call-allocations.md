---
title: Substitution allocates fresh Var leaves for id(Γ) and a fresh memo table per call
status: closed
labels: [kernel,performance,substitution]
area: kernel
created: 2026-11-02
updated: 2026-11-02
---

Cut substitution's per-call allocations: the identity substitution builds |Γ| fresh `Var` nodes, and every traversal grows a fresh memo table.

## Problem

- `LocalSubst::id(ctx)` (`crates/kernel/src/subst.rs` ~2263) allocates `|Γ|` new `Arc::new(Term::Var(..))` leaves, 144 bytes each. That happens every time a β-substitution is formed, `LocalSubst::id(&gamma).extended(arg)`, for example once per explicit argument in `elab/src/application.rs` ~796. There are 200 `LocalSubst::id(` call sites and 276 literal `Rc::new(Term::Var(` sites.
- Every pure `Mapper` call constructs a fresh `NodeMemo` (two `HashMap`s, `subst.rs` ~2000–2016, ~1412). It grows from empty by rehashing and is dropped with its keep-alives.

Measured with the gdb sampler (`docs/surveys/data-oriented-survey.md` §5): `id(Γ)` is in 1.3–3.7% of cold samples, and memo inserts (`subst.rs` ~406, ~511, mostly allocation and rehash) in 3.0–7.4%.

## Proposal

- **Shared leaves.** `Term::var(i)` hands out an interned `Arc<Term::Var(i)>` for `i` below a bound (e.g. 4 096); `Zero`, `TmNat` and `Type::Nat` get the same treatment. `id(Γ)` becomes `|Γ|` refcount increments. Extra sharing only helps the identity-keyed memos, and leaves are answered before any memo is consulted.
- **Reused memo tables.** A thread-local pool of `NodeMemo`s, cleared with capacity kept when a call ends.
- Not proposed: a lazy identity prefix in `LocalSubst`. The paper's `id_Γ` is fully expanded, and that would be a representation change to the substitution calculus.

## Cost and risk

Local to `subst.rs` and `term.rs`. Interned leaves shared across kernel workers mean contended atomic refcounts, so prefer per-thread intern tables (leaves stay `Send`), and measure with `scripts/perf ab` at width 8 as well as 1. Counters such as `local_subst_nodes` and `subst_memo_hits` must not move except where address-keyed memos already vary run to run.

## What it assumes from elsewhere

- **[[subst-rebuild-then-discard]]** owns the rebuild-then-drop pair. Assumed here: nothing; the two are independent.
- **[[kernel-arena-terms-frozen-prefix]]**: under arenas both allocations disappear. Assumed here: only that the arena is not imminent.

## Log

- 2026-11-02: Built (branch claude/project-thread-7z45uf). `Term::var_rc`/`var_rcs_descending` (term.rs) hand out per-thread interned `Var(i)` leaves below 4 096; `LocalSubst::id` is `|Γ|` refcount increments, and `sub_tm` interns every `Var` it outputs (`Term::into_rc`). A `Var` leaf is mapped *before* the shared-node memo is asked and enters it only when it became a payload: the first cut skipped the memo for `Var` outright, and `a_shared_chain_stays_shared_through_shift_and_substitution` caught the payload being copied apart along two paths. `NodeMemo`'s tables come from a per-thread pool (8 tables, kept only up to capacity 4 096, since `clear` costs capacity) and go back emptied, so keep-alives still die with the call.

  Counters (perf ab, calc_parser, widths 1 and 8): `subst_memo_hits` −9% (leaf hits gone), `syntax_eq_nodes` −0.3–0.5% (equal leaves are now `ptr_eq`). One behaviour move, benign: `parser_diagnostics::commit_chain` gates 12 fewer declarations, because `grind`'s host hands out one handle per shared subterm (`host.rs` `issue_shared`, keyed by scope and address, never under a binder), and the same variable is now one node. Seconds: −2.0% wall at width 1 and −0.7% at width 8, both inside the per-sample spread, so no time result.

  Not done: `Zero`, `TmNat`, `Type::Nat` interning, and the 311 literal `Rc::new(Term::Var(..))` sites (schemas and tests, off the hot path).
