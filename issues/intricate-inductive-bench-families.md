---
title: Bench large and intricate inductives at growing size, with recorded exponents
status: closed
labels: [inductives,performance,benchmarks,elaboration]
area: language
created: 2026-10-26
updated: 2026-10-26
---

The frontend bench had one wide-inductive family (`scale/wide-inductive`,
one `Nat` field per constructor and one `match`) and the forded/indexed
families, which sweep a lowering's own multiplier. Nothing measured the two
shapes the native and metatheory work is heading for: an instruction set's
worth of constructors with operand fields, and the typed syntax of an object
theory (mutual sorts, judgment-indexed terms, function-field premises).

Scope: families under `scripts/bench-frontend` that sweep each shape along
the axis that makes it large, split so a slope names the phase (declaring,
constructing, eliminating, converting), each stating its lower bound; issues
for any blowup found.

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the harness and its regression rules.
  Assumed here: only that a family is a generator plus sizes.
- **[[tactic-scaling-bench-families]]** set the conventions these follow:
  a lower bound per family, bands as the measurement ±0.35, slope rows only
  in the baseline when recorded off the recording machine.

## Log

- 2026-10-26: LANDED: ten families in `crates/elab/benches/frontend/fixtures/intricate.rs`, `scripts/bench-frontend --filter inductive/`. Each family's doc comment and its row in `docs/frontend-benchmarking.md` states its lower bound. Slope rows are in `baseline.tsv`; case and split rows wait for a `--save` on the recording machine. Release, 4-core cloud box; slope as the mean of three runs (range), and one run's min time and probe-run split at the largest size:

    | family | sizes | largest | elab / kernel at largest | slope (range) | lower bound |
    |---|---|---|---|---|---|
    | `isa-declaration` | 32..512 forms | 100 ms | 92% / 5% | 0.99 (0.95-1.03) | 1, met |
    | `isa-constructor-use` | 32..256 forms | 1.13 s | 94% / 6% | 1.71 (1.66-1.79) | 1 |
    | `isa-opcode-match` | 32..256 forms | 423 ms | 88% / 12% | 1.62 (1.52-1.70) | 1 |
    | `isa-roundtrip` | 16..128 forms | 1.76 s | 20% / 80% | 2.15 (2.14-2.18) | 1 |
    | `enum-equality` | 8..64 ctors | 1.29 s | 34% / 65% | 2.51 (2.40-2.60) | 2 |
    | `record-fields` | 8..64 fields | 73 ms | 29% / 70% | 1.42 (1.11-1.58) | 1 |
    | `mutual-declaration` | 2..16 members | 6.4 ms | 96% / 2% | 1.49 (1.47-1.50) | 1 |
    | `mutual-recursion` | 2..5 members | 4.23 s | 3% / 96% | 2.82 (2.71-2.95) | 1 |
    | `typed-syntax` | 5..8 ctors | 3.00 s | 5% / 95% | 1.78 (1.45-1.99) | 1 |
    | `function-fields` | 2..8 ctors | 903 ms | 3% / 98% | 1.67 (1.63-1.75) | 1 |

    - **Three blowups, filed, each against a control that does not pay it.** (1) [[wide-inductive-constructor-mention-cost]]: a constructor value of an n-form type is Θ(n²) in elaboration whichever constructor (`respell_spine`'s positional guard compares every spine component by deep `Type` equality; gdb, six of six samples), plus Θ(k·n) gate for the k-th; `I₀(a, b)` at 512 forms is 363 ms. (2) [[mutual-group-recursion-gate-cost]]: recursion over an m-member group is ~m^2.8 and 96% gate, and the one-step `refl` is kernel `OutOfFuel` at m = 8; the same twelve constructors as one inductive check in 5 ms against 6.4 s for the six-member group. (3) [[indexed-family-recursion-gate-cost]]: typed-syntax and function-field recursion are gate-bound and superlinear past the sweep (CLI: ~3.2 from 5 to 12 constructors, ~3.4 from 8 to 16), with a quarter-second `refl` constant at five constructors; a plain child instead of the function field is 60× cheaper at 16.
    - **Smaller debt, not filed separately.** `isa-opcode-match` (an n-arm match into `Nat`, no constructor values) is ~1.6 and almost all elaboration; `enum-equality` is half a power over its n² arms, mostly gate; `record-fields` and `mutual-declaration` sit around 1.4-1.5. Recorded in the bands so a fix shows.
    - **Sizes.** The intricate families stop where a run costs a few seconds (five members, eight constructors), so their slopes understate the curve past the sweep; the filed issues carry the larger CLI points. The added families cost a few minutes per full run of `--filter inductive/` on the cloud box, most of it `mutual-recursion` and `typed-syntax`.
    - **Limit met.** A family takes one index (`docs/inductive-indexed-lowering.md` §8.4, owned by [[indexed-families]]), and an index type needs two constructors, so typed terms are `Tm(J(Γ, A))` over `inductive Jd { J(g: Cx, t: Ty), WfCx(g: Cx) }`. The fixture asserts the `IWf` route (and `IwfW` for the function fields).
