---
title: Free-variable bounds tax one-shot checking ~1.4x; accepted, with levers if it grows
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

[[subst-visits-closed-subtrees]]'s round left one deliberate regression:
**code/check-identity-recursor 440 → ~610 µs (~1.4×)**, re-recorded in
`baseline.tsv` on 2026-07-31. This issue owns that number: why it is
accepted, what was already tried, and which levers exist if a real workload
ever makes it matter.

## Why it happens

The bounds memo (`crates/kernel/src/bounds.rs`) pays per *queried* node —
a marker write on first sight, a bounds walk + cache entry on second, a
probe per traversal thereafter — and one-shot checking of fresh code terms
is the workload where none of that ever amortizes: `check_term` of a code
recursor builds its 52 branch telescopes fresh (`rec.rs`), traverses them
once, and drops them. Worse, the identity recursor's branches are saturated
with `u^δ`/`U^δ`, whose tails a β-substitution genuinely rewrites (the
target context shrinks), so `has_tail` makes those regions *correctly*
unskippable: the metadata is all cost and no skip there.

## Why it is accepted

The same mechanism on the same commit buys, on real re-traversal workloads:
`heather check lib/ir_v1.hthr` 107 s → 13.6 s release (7.9×),
`wf/mirror-involution` ~9×, `conv/simulate-payload` slope 0.91 → 0.00.
Turning off just the `ShiftLocal` half — the half this bench mostly pays
for — recovers the bench to 1.0× but costs ir_v1 13.6 s → 40 s: the
payload-shift-under-binders case (an inlined interpreter substituted under
an eliminator's binders) is exactly the real workload's dominant cost.

## Already tried, with measurements (2026-07-31)

- `HashMap` memo, eager compute-on-miss: 1.5–2.0×.
- Refcount gate (skip memo when `strong_count == 1`): broke the wins —
  sharing that makes a hot payload's count ≥ 2 is transient (the sharing
  output dies within a step), so slopes reverted to ~1 — and still 1.4×.
- Direct-mapped fixed cache (no growth/flush): 1.5×.
- Two-stage with keep-alive markers: 1.5× (marker Rc churn tripled
  `drop_slow`).
- Two-stage with **bare-address markers** (shipped): 1.35–1.4×.

## Levers if a workload ever pays this for real

- Query throttling by traversal phase (don't query inside regions a parent
  already proved unskippable *for the same reason* — needs care: closed
  children hang off touched spines, which is where wins live).
- Tail summaries instead of a boolean `has_tail` (skip when the δ being
  applied provably fixes every tail: needs uniform `len − depth` and base
  stability; β-substitutions never qualify, so this only pays for
  weakening-shaped δs).
- A `Cell`-free single-borrow query path (the thread-local + `RefCell`
  handshake is ~5% of the bench).

## What it assumes from elsewhere

- **[[subst-visits-closed-subtrees]]** owns the skip mechanism and its
  soundness story. Assumed here: only that skips are decided per-node from
  the memo in `bounds.rs`.
