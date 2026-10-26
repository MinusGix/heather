---
title: Bench rewriting and let fan-out at growing size, with recorded exponents
status: open
labels: [tactics,performance,benchmarks,proofs]
area: tactics
milestone: [tac-general]
created: 2026-10-26
updated: 2026-10-26
---

The frontend bench (`crates/elab/benches/frontend`,
`docs/frontend-benchmarking.md`) has no tactic family and no let fan-out
family. Shapes with known linear lower bounds are therefore unguarded:
nothing records that one `rewrite` on a let-shared goal is 2^k
(`docs/mengine-survey.md` §4.2), and nothing would notice if the planned
relational rewriting ([[rewrite-setoid-relations]]) inherited a quadratic.

mengine's benchmark suite (`benchmarks/` in
<https://github.com/triviajon/mengine>, survey §1.6) is a ready list of
generators that Rocq and Lean are measured against, each small:

| family | goal | lower bound |
|---|---|---|
| `rewrite/fa` | `g(f(f(…f(a))))` to `g(a)` by `h: (x) -> f(x) = x` | linear in n |
| `rewrite/repeat-mod` | `(… (b mod p) mod p …) mod p` to `b mod p` | linear in n |
| `rewrite/let-addr0` | `let vᵢ = vᵢ₋₁ + vᵢ₋₁ + 0` chain, remove the `+ 0`s | linear in the lets (the sites are 2^k as a tree) |
| `rewrite/let-nary` | `let xᵢ = f(xᵢ₋₁, …, xᵢ₋₁)` (arity n, m lets), rewrite `f(x, …, x) = x` | linear in n·m |

Add [[proof-let-substitution-cost]]'s `fan` and `dep` (the let chains
themselves, checked by `refl`), which isolate the gate's share.

## Notes for the fixture

- The suite's headline is a log-log slope. A family that is exponential
  today shows a slope that rises with size, so pick sizes where the run
  stays under the wrapper's rail, record the slope as it is, and let a fix
  move it. A family that cannot run at three sizes is not yet a family; use
  `have.rs`-style exact-counter assertions instead.
- What Heather can state today: `rewrite/fa` needs one `rewrite` per `f`
  (each rewrites one instance), so it measures n walks of an n-node goal
  until a repeated or bottom-up rewrite exists. Record that as the
  baseline; it is the number [[rewrite-setoid-relations]]'s bottom-up
  design should flatten.
- `--timings` gives frontend and gate apart; keep both columns, since the
  2026-10-26 probe found both growing.

## Acceptance

- The families run under `scripts/bench-frontend` with baselines saved.
- Each family's README line states its lower bound, so a reader can see
  which slopes are the target and which are debt.

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the harness and its regression rules.
  Assumed here: only that a family is a generator plus sizes.
- **[[kernel-typing-memo-on-node-identity]]** and
  **[[subst-shared-node-memo]]** own the let fan-out costs. These families
  are their measurements, not their fixes.
