---
title: A match on a λ-bound trace whose type is IsTrace of a tier-2 constructor costs the kernel ~100×
status: open
labels: [kernel,performance,interaction-trees]
area: language
created: 2026-10-22
updated: 2026-10-22
---

Four library proofs had the same shape: a statement whose type unfolds to a
Π over a trace, `(tr) → IsTrace(E, Vis(c, k), tr) → …` (`Sim`,
`ITree::Implements`, `NextTrace` at `Calls`), proved by a λ that binds the
trace witness — annotated `(w: VisTrace<…>(…))` or not, the elaborated term is
the same, the verdict cache says so — and `match`es on it. Their kernel gates
were large for what they do:

| proof | before | lemma form |
| --- | --- | --- |
| `linux_trees::ITree::implements_sized` (Vis arm) | 5.76M steps | 33k steps |
| `linux_x86_64_sim::sim_vis` | 3.65M steps | 171k steps |
| `linux_x86_64_wp::wp_next_runs` (Calls arm) | 1.1M steps | (lemma form, not re-measured alone) |
| `stream_filter_spec::filter_sends` (both calls) | 7.74M steps | 357k steps, the two lemmas and the rest |

The **lemma form** states the same arm as a theorem whose parameter is
`w: VisTrace<…>(Events::linux(), c, tr, λ a rest => IsTrace(…, k(a), rest))`
and matches there; the original λ passes `w` on. That is what landed
(2026-10-22, [[linux-wp-cold-rail]]): `ITree::implements_sized_vis`,
`sim_vis_trace`, `wp_next_calls_runs`, `filter_sends_reading`/`_writing`. The `Ret`/`Cut` arms of the same
matches were cheap in place.

Not understood: why. The suspicion is that in place, `w`'s type in the core
term is `IsTrace(E, Vis(c, k), tr)` (the expected domain, not the
annotation), so every kernel use of the match — the eliminator's scrutinee
type against its indices, each arm's motive instance — converts through
`IsTrace`'s W-recursion over the tier-2 `Vis` node and its leaf predicate,
where the lemma's parameter is already `VisTrace` syntax. Probe pairs are
cheap to rebuild: copy one of the old proofs into a scratch module with an
extra unused `salt: Nat` parameter (so the verdict cache does not answer it),
next to its lemma form, and `heather check --cache --timings`.

## Levers

- Elaborator: give a λ binder its annotation as the core binder type when
  the annotation converts with the expected domain (the kernel checks that
  conversion once), or the scrutinee's whnf'd type at a `match`.
- Kernel: find what the in-place form converts repeatedly
  (`--timings` steps per arm, or the conv-miss sampler under
  `value-metrics`) and whether a memo would catch it.

Acceptance: the in-place spelling of `sim_vis` gates within a small factor
of `sim_vis_trace`.
