---
title: Keep a shifted DAG a DAG: memoize shared nodes within one local traversal
status: closed
labels: [kernel,performance,proofs]
area: kernel
created: 2026-10-26
updated: 2026-10-26
---

A let alias used below the depth it was bound at is
`a.term.shift_local(by)` when it is not a splice (the alias arm in
`crates/elab/src/lib.rs`), and
`subst.rs`'s `Mapper` has no per-traversal memo, only the closed-subtree
skip of `bounds.rs`. A subterm reached along two paths is rebuilt on each, so
a shared value comes back from the shift as a tree. This is cause 2 of
[[proof-let-substitution-cost]]'s diagnosis, and
[[kernel-typing-memo-on-node-identity]]'s reach section asks for it to be
named or filed: the typing memo cannot share what the shift has already
copied apart. mengine, a λ-DAG proof engine, keeps the same memo on by
default for this reason (`docs/mengine-survey.md` §3.2). It has no shift at
all; the memo is how an indexed kernel gets the same property.

## The proposal

Within one `map_term`/`map_type` call, memoize the result for a node keyed
by its `Arc` address and the traversal's `Depths`, with a keep-alive clone so
the address cannot be reused while the memo lives. Drop the memo when the
call returns.

`issues/whnf-sharing-term-growth.md` measured such a memo inside
`apply_local` at 0.05% hits and a slowdown. That workload had no sharing
left when substitution ran, and this one does. So gate the memo: consult it
only for nodes whose `Arc::strong_count` is above one. A count perturbed by
the bounds cache's keep-alive entries only changes which nodes are probed.
The result is the same term either way, so this memo, unlike the typing
memo, needs no determinism argument: it changes allocation and work, never
syntax or a verdict.

## Acceptance

- [[proof-let-substitution-cost]]'s `fan` family, with each alias used
  under a binder (a `λ` continuation over the chain, the print proof's
  shape), is linear in the shift's node visits. Count visits with a stats
  counter so the claim is exact.
- `scripts/bench --check` shows no regression on the `subst` and `nat`
  families (`nat/step-once` is the refcount-dense one).
- The 300-seed substitution laws pass unchanged (the memo is invisible to
  them by construction; they are the control).

## What it assumes from elsewhere

- **[[kernel-typing-memo-on-node-identity]]** owns checking a shared node
  once. Assumed here: only that it shares nodes the elaborator hands it
  unshifted, so this issue is what extends its reach to aliases used under
  binders.
- **[[open-payload-shift-copies]]** owns the copy of an open payload per
  occurrence during β-substitution. That is a different traversal (a
  payload copied once per variable occurrence, not a DAG walked as a tree),
  though a memo keyed by payload address and depth would serve both.

## Reach

Module images (`module_image.rs::put_term`) also write trees. Nothing has
measured an image as tree-blown since `have` removed let fan-out from the
library; the trigger is an image whose node count far exceeds the term's
shared size, which [[let-fanout-diagnostic]]'s tree-versus-shared count
would show.

## Log

- 2026-10-26: LANDED. Three places lost the sharing, not one.
    - **The kernel traversal** (`subst.rs` §Keeping a shared DAG shared): a per-call `NodeMemo` keyed by node address and `Depths`, consulted only for `Rc::strong_count > 1`, with a keep-alive per entry and the change counter replayed on a hit. Every pure mapper opts in: the local shift and substitutions (`ShiftLocal`, `SubstLocal`, `InstTop`) and also the global and universe ones. The global ones turned out to matter: with only the local memo, the elaborated body of the `fan`-under-`λ` probe was a DAG, but `commit` rescopes every body with `shift_global_above(..).apply_global(σ)`, and that walk handed Ψ a tree again (shifting the committed body at k = 16 visited 524,290 nodes). `AbstractLocal` (occurrence numbering), `ReindexGlobal` (a callback per variable), `RootTerms` and `RebuildChecked` stay out. Debug builds re-walk behind a sample of hits, on the skip sampler.
    - **The alias** (`elab` `context.rs`): an alias used at several deeper binders was shifted per use, so a later `let` built from two uses held two separate copies, and a chain with a binder between every link doubled per link even with the memo. `Alias::at(by)` now shifts the value and type once per depth (`Alias::shifted`); `splice`, `resolve_at` and `subst_local` go through it.
    - **Counters**: `local_subst_nodes` (nodes the local shift/substitutions visited) and `subst_memo_hits`; `scripts/timings` columns `local` and `subst memo`.
    - **Acceptance 1**: `crates/elab/tests/let_and_blocks.rs::a_shared_let_chain_stays_shared_under_binders`, with a test gate that admits everything so the counter sees elaboration alone. Chain under one `λ`: elaboration and a further shift of the committed body are linear in k. A binder between every link: elaboration is **quadratic** (each link shifts the previous link's value, whose size is its depth; a shift of a shift is a fresh copy, which is [[open-payload-shift-copies]]'s representation question), the committed body is linear to shift; both were 2^k. The kernel unit test `a_shared_chain_stays_shared_through_shift_and_substitution` pins `shift_local`/`apply_local` on a 24-link chain: ≤ 8k visits and every output link's two children `ptr_eq`.
    - **End to end** (release, width one, `--timings`, whole `chain` item including the gate): the interleaved probe at k = 8/12 went 5,058 → 1,242 and 81,834 → 16,854 local visits. What is left is the gate's own walk, one per path: `queries` are unchanged (1,032 / 16,396), as they must be until [[kernel-typing-memo-on-node-identity]] lands. That issue's Reach now holds: aliases used under binders reach the gate as shared nodes.
    - **On a real workload**: `heather check lib/native/native_cat_executable.hthr --cache`, master's binary against this one (release, width one, cold verdicts): `queries` identical on every item, and no item's count goes up. `shift_global_nodes` fell 1.12G → 274M summed over items (the global rescoping's own share of shared nodes), and 428 items trade a few `conv_misses` and eval steps for `conv_memo_hits`, since more of what reaches the gate is shared. Seconds are not measured here (one cold sample each on the cloud box).
  - **Acceptance 2/3**: `scripts/bench --check --filter subst` and `--filter nat` pass shape-only on the cloud box (the baseline is another CPU and toolchain, so no time verdict); the 300-seed substitution laws pass in the suite unchanged.
  - Not done, with owners: `rewrite`'s abstraction walk (`AbstractLocal`) is still a tree walk; a memo for it must number occurrences of a shared subterm, which is the bottom-up design of `docs/mengine-survey.md` §4.3. Module images (`put_term`) still write trees; nothing has measured one as tree-blown (this issue's Reach).
