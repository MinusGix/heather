---
title: Bench rewriting and let fan-out at growing size, with recorded exponents
status: closed
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

## Log

- 2026-10-26: LANDED: seven families in `crates/elab/benches/frontend/fixtures/rewriting.rs`, run by `scripts/bench-frontend --filter rewrite/` and `--filter let/`. Each family's doc comment and its row in `docs/frontend-benchmarking.md` states its lower bound (all linear); the bands record today's slope. Slope rows are in `baseline.tsv`; case and split rows wait for a `--save` on the recording machine (the bands come from a 4-core cloud box, and its times would sit under the baseline's other `env`). Release, cloud box, one run's min times and its probe-run phase split at the largest size; slope as the mean of four runs (range):

    | family | sizes | largest | elab / kernel at largest | slope (range) |
    |---|---|---|---|---|
    | `rewrite/fa` | n = 16..128 | 62 ms | 28% / 72% | 1.44 (1.33-1.53) |
    | `rewrite/repeat-mod` | n = 16..128 | 120 ms | 34% / 66% | 1.82 (1.75-1.87) |
    | `rewrite/let-addr0` | k = 6..12 | 157 ms | 69% / 31% | 5.60 (5.40-5.73), ×4 per two lets |
    | `rewrite/let-nary` (3 lets) | arity 4..32 | 51 ms | 90% / 9% | 2.05 (1.89-2.20) |
    | `let/fan` | k = 32..256 | 12 ms | 64% / 13% | 1.10 (1.00-1.17) |
    | `let/dep` | k = 8..64 | 336 ms | 91% / 9% | 2.55 (2.53-2.59) |
    | `let/stmt` | k = 14..20 | 93 ms | 50% / 49% | 9.58 (8.78-9.99), ×4 per two lets |

    - **What the split says.** `rewrite/fa` and `repeat-mod` are gate-dominated at size: n rewrites nest n `J`s, each over an O(n) motive, which fits about n². `rewrite/let-nary`'s gate stays small (the typing memo shares it), and its elaboration grows with the n³ tree, which is survey §4.2's abstraction walk or occurrence matching (not split). `let-addr0` is 2^k in both halves.
    - **`let/dep` is mostly elaboration now**, and the elaboration grows faster than the gate's quadratic: ×6.7 from k = 32 to 64 (`heather check --timings`, width one: 28 / 293 / 2,246 / 26,788 ms total against 3.8 / 21 / 122 / 1,518 ms gate at k = 32 / 64 / 128 / 256). Logged on [[discarded-let-values-nest-binders]], whose acceptance counts gate queries only.
    - **`let/stmt`'s elaboration is 2^k too**, alongside the gate's `Term::eq` walk. Logged on [[kernel-equality-walks-dags-as-trees]].
    - **Limits met on the way.** `rewrite` rewrites one instance per equation, so a family is n equations in one `rewrite(h, …, h, refl)` (a control with n − 1 fails at `refl`). The goal `f^256(a)` exceeds the expression depth limit (512), so `fa` and `repeat-mod` stop at 128.
    - **Bands** are the mean ±0.35, or the four-run range where that is wider (`let-addr0` 5.00-6.20, `stmt` 8.40-10.80): on an exponential curve a fixed cost at the small end moves the fit, and the band only needs to notice a fix, which drops the slope to about 1.
