---
title: A goal query copied all of Ψ, so a program's proofs cost what its build had loaded before them
status: closed
labels: [perf, elaboration, x86]
code: crates/elab/src/goals.rs:559 @ 4cbe35d
created: 2026-10-03
updated: 2026-10-03
---

`GoalArena::world` built the world a goal statement is read in by
`psi.bindings.to_vec()` plus the goal slots, then `GlobalCtx::new` — a copy of
every binding of Ψ per call, and a drop of it after. `split_all` and the
arithmetic tactics ask for that world per stuck-scrutinee search and per
simplified subterm (`goal_combinators::simplify_goal::term`,
`stuck_scrutinee`), so a tactic proof's elaboration cost scaled with the size
of Ψ, not with the proof. Ψ is persistent and chunked precisely so that this
need not happen (`crates/kernel/src/term.rs`, `GlobalCtx`); four call sites
flattened it anyway: `GoalArena::world` and `delta_world`,
`Elaborator::refresh_delta_psi` and `prefix_world`, and
`SemanticOracle::with_dynamic`.

## How it showed

A `build-x86` of `examples/x86-native/wc.hthr` checks the bundled library and
the `Fields` formatter's two certificates (~15.7k generated declarations)
before the program. The program's four `split_all; all_goals { omega }`
proofs and `Filter`'s default `advances` field then cost about four times
what the same declarations cost under `heather check` of the same file, with
**identical counters** (steps, misses, queries): the work was the same, the Ψ
it ran beside was not. A poor man's profiler (gdb stack samples) during the
program's module put ~84% of samples in `GoalArena::world` →
`GlobalBindings::to_vec`, or in dropping the resulting `GlobalCtx`.

## Fix

`GlobalCtx::extended` (clone, then push: shares every sealed chunk, copies
at most one tail) and `GlobalCtx::prefix` (shares the full chunks of a
prefix, copies at most one chunk). The five sites build their worlds with
those. The worlds are equal binding for binding to the ones built before
(kernel unit test `prefix_and_extension_agree_with_rebuilding`), so nothing a
judgment sees changes; only the copying goes.

## Result

`scripts/perf ab` (cold, width one, two interleaved samples, 2026-10-03,
cloud box; counters identical across binaries and samples):

- `examples/x86-native/wc.hthr` build: total 335–340 s → 234–241 s, −29%,
  samples separate. The `wc` module (the program's own proofs) 125 s → 26 s;
  everything else within noise.
- `lib/elf64_read_fields.hthr` check: no change (spread exceeds the delta).
  Its Ψ is the library alone and its proofs do not split, so it never paid
  this; [[read-fields-process-cpu-margin]] is not moved by it.

The scaling was with Ψ's size, so any frontend tactic run late in a large
session (a program after its certificates, a module late in a long check)
paid it; the wc build is where it was largest.

Related: [[x86-certificate-per-declaration-constant]] (the re-attribution
that found it), [[context-representation-clones]] (why Ψ is chunked).
