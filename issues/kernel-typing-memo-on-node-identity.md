---
title: Memoize kernel typing on node identity, so a shared let value is checked once
status: closed
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
- 2026-10-26: LANDED. `typing.rs` §The typing memo: one gate's `Tc` keeps, per node and scope, an elimination form's inferred type and the expected types an intro form checked against (`Judged`, keyed by `Scope`).
    - **Key**: the node's address plus Ψ's and Γ's identity tokens, Γ's base, the layer, `|L|` and the `box` bit, which are everything a rule reads besides the node. Each entry owns the node and both tokens. `tm_check`/`tm_infer` now take the node as `Rc<Term>`, which is what the entry keeps alive (every recursive call site already held one; the five public entry points wrap their root).
    - **Which nodes**: by kind, never by count. Inference is kept for the eliminations (applications, projections, the recursors, `UApp`/`CtxApp`/`TyApp`, `letbox`, `out`), which are also how checking reaches a shared value; checks are kept for the structural check forms (the four λs, `box`, the unannotated `pair@`/`inl@`/`inr@`), up to four expected types per node and scope. Nothing is evicted and failures are not kept, so whether a lookup hits is a function of the input. The unit test `reference_counts_do_not_move_the_counters` holds an extra reference to every node and asserts identical counters.
    - **Trusted base**: debug builds re-judge a sample of hits on the `checks.rs` stride and assert the memo's answer. The re-judging runs under the new `stats::unobserved`, so debug and release builds count alike. Off under the spelling record (`spell_checked_in_code`). Recorded in `crates/kernel/DESIGN.md`.
    - **Counter**: `typing_memo_hits` (raw column; one per second or later path into a node in one scope).
    - **Acceptance 1** (release, width one, `--timings` queries; probes as in `docs/mengine-survey.md` §4.2 and [[subst-shared-node-memo]]):

      | family | k = 8 | 16 | 32 | 64 | master (at k) |
      |---|---|---|---|---|---|
      | `fan` | 36 | 68 | 132 | 260 | 262,144 (16) |
      | chain under one `λ` | 39 | 71 | 135 | 263 | 16,387 (12) |
      | binder between links | 44 | 84 | 164 | 324 | 16,396 (12) |
      | statement (`stmt`) | 143 | 287 | (431 at 24) | | 786,425 (16) |
      | transparent (`refl` over the chain's value) | 84 | 148 | 276 | 532 | |
      | `dep` (a proof `let` at every link) | 308 | 868 | 2,756 | 9,604 | 2,883,512 (16) |

      `dep_16` no longer runs out of fuel on master either (2.9M queries, about 2 s on the cloud box). It checks now in 868. `dep` stays quadratic: each unused proof `let` is checked around the rest of the block under its own binder, so the chain reaches the gate at `k` depths, as `k` separately shifted copies, and the memo judges each once. Filed as [[discarded-let-values-nest-binders]]. Pinned by `crates/elab/tests/let_and_blocks.rs::a_shared_let_chain_is_checked_once_per_link` (fan, under, interleaved and transparent linear from k = 16 to 32; `dep` at 16 under 4,096 queries) and the kernel unit test `a_shared_chain_is_judged_once_per_link` (40 links, exactly 39 hits). `have.rs`'s fan-out test lost its `let` control, which no longer fans out.
    - **Acceptance 2**: `scripts/bench --check` flags `conv/perturbed-pairs` and `check/generated-terms` slopes on the cloud box. Master's tree (`3ea9c92`) flags both by the same margin on the same box, so they are this box against a baseline recorded on another CPU, not this change. `code/check-identity-recursor` is flat (slope 0.03).
    - **Acceptance 3**: `lib/std/num/rat.hthr` at widths 1 and 8: every count column is identical except on 16 `instance` items whose `check_terms` differ by width, and master differs on exactly the same 16 items (gate scheduling, not the memo). `local_subst_nodes` and `cow_copies` move between runs of one binary on master too (perf ab reports them as unstable).
    - **On real workloads**, counters only (seconds on this box are not a result): `scripts/perf ab` on the showcase moved `conv_shortcut_hits` −16%, `conv_misses` −11%, `eval_steps` −7%, with 3,346 memo hits, kernel-gate seconds unchanged and RSS within the spread. `lib/std/num/rat.hthr`: queries 738,510 → 681,662, misses −6%.
    - **Residue in the gate: equality.** `stmt`'s queries are linear, but its gate *time* still doubles per link (2.9 / 72 / 787 ms at k = 16 / 20 / 24, release; every query a shortcut hit, no misses, no eval steps; k = 32 exceeds the 300 s rail). Its two sides are elaborated separately, so `refl`'s check compares two equal DAGs, and the derived `Term::eq` walks them as trees (`gdb`: all frames in `<Term as PartialEq>::eq`). Filed as [[kernel-equality-walks-dags-as-trees]].
  - Not done: mengine's child-pair key for applications (separately built `f a` nodes over shared children). Nothing measured here needs it, and `typing_memo_hits` against `queries` would show it if something does.
