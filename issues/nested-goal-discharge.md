---
title: Allow a hole inside an `on` right-hand side
status: open
labels: [frontend,elaboration]
area: language
created: 2026-07-24
updated: 2026-07-24
---

[[goal-holes]] refuses a hole inside an `on` right-hand side:

```heather
theorem t(n: Nat): add(n, 0) = n {
    ?p
    on ?p := ?q;      // error: a hole may not appear in an `on` right-hand side
}
```

## Why it is refused rather than broken

Two kernel-level facts, both from `crates/kernel/src/subst.rs`:

1. A `GlobalSubst`'s payloads are **not telescoped among each other** — they
   are all scoped in the source Ψ. So a payload that itself mentions a goal
   would simply not be substituted: one σ application cannot close a
   discharge chain.
2. An `on` RHS is elaborated *in* the goal world (it must be — the goal's Γ
   and statement live there) and its solution is then strengthened back down
   by `G` with a dummy-payload σ. That strengthening is sound **exactly
   because** no goal occurrence survives in the payload to meet a dummy.

The `frozen` flag in `crates/elab/src/lib.rs` is what enforces (2), and it
is load-bearing, not defensive: relaxing the restriction without replacing
the strengthening step would silently produce wrong terms rather than an
error. (The kernel would still gate them — this is a
correctness-of-elaboration issue, not a soundness one.)

## What lifting it takes

Discharge in dependency order instead of source order: build the graph of
"goal A's solution mentions goal B", reject cycles with a diagnostic, then
substitute in reverse topological order (or iterate the σ to a fixpoint,
bounded by the goal count). Each solution is strengthened only once every
goal it mentions has been substituted away.

## Why it matters later

[[surface-proof-automation]]'s `apply` is the concrete consumer: the
multi-premise form (`apply trans` leaving two goals) is "defer f's
arguments", and a natural desugaring wants to place holes inside the
discharge it generates. Until this lands, such a desugaring must put its
holes in the block body instead.

Also the natural spelling of docs/sketches/surface-v3.md §2's goal-merging
idiom: today the strong goal must be introduced with a `let`
(`let strong: P = ?g;`), which works and is tested, but discharging one goal
*from* another directly is the shape the sketch reaches for.

## Log

- 2026-11-05: gardener: cites a file it shares with [[lsp-from-the-meta-layer]] (`docs/sketches/surface-v3.md`); [[surface-syntax]] (`docs/sketches/surface-v3.md`); [[warm-replay-relocate-cost]] (`crates/kernel/src/subst.rs`).
