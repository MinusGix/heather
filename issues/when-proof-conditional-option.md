---
title: Build When<T, P>, a value present exactly when P holds
status: open
labels: [language,elaborator,library]
area: language
created: 2026-11-14
updated: 2026-11-14
---

`When<T, P>`: a value that is there exactly when `P` holds. Minus's
"proof-conditional Option" (2026-11-14), designed in `docs/when-design.md`,
which owns the type, the tested call, the flow facts, `?` and the coercion.

The issue tracks the build, one PR per stage (`docs/when-design.md` §9):

1. The type and its library, `lib/std/core/when.hthr`, probes in
   `lib/_tests/std/core/when_tests.hthr`.
2. The tested call: a proof-taking call where a `When` is wanted leaves its
   condition out and tests it (no keyword; Minus 2026-11-14 declined a
   `checked` prefix). Run the §7 probes here.
3. Flow facts (`if let` leaving `¬P` in `else`) and `val`'s `known` search.
4. `?` in a function returning `When<U, Q>`, with `Q` stated, on a `When`
   or a proof-taking call.
5. Coercion of a `When<T, P>` to `T` with `P` found, with `scripts/perf ab`
   benchmarks.

Open for Minus (§10): the name, whether `if let`'s negative
evidence is for `When` alone.

## What it assumes from elsewhere
- **[[found-proof-differs-across-recursion-companions]]** (closed) owns the
  lifting of found proofs out of `decreases` bodies. Assumed here: only
  that a proof-taking function's condition is a parameter whose default is
  a context search, as `Vec::at`'s is (PR #607).
- **[[if-evidence-hidden-from-tactics]]** owns the `__if_bitN` names; stage 3
  reuses the device for `if let` evidence.

## Log

- 2026-11-14: Stage 1 merged (PR #609). Minus 2026-11-14: no `checked` keyword ("generalize `?` or another elegant spelling"); the call is tested where a `When` is wanted; coercion `When → T` is wanted as its own PR with benchmarks (stage 5). Stage 2 built: `crates/elab/src/tested.rs`, the first omitted condition is tested and later ones searched with its proof in scope (the design thread agreed: better than the conjunction). §7 probes: a tested read in a `decreases` body needed the unfolding walk to type the scrutinee as its test; neutral-condition proofs go by `When::of_cases`. Stage 1's claim that `vector_index`'s `same` is `refl` was wrong; `vector_index_irrel` added.
- 2026-11-14: Review of #612 (design thread): arm constructors are resolved rather than read by spelling, and `is_when` reads the inductive's tag before any lookup (`when_names_tests`). `scripts/perf ab --base master` over omega, nat, list, calc_parser (cloud, cold, 3 samples, loaded box): 45 counters identical; seconds within spread except calc_parser wall −1.3 % (separate). Stages 3–5 built on it. Stage 5 coercion, `perf ab` stage 4 → stage 5 (cloud, cold, 3 samples, loadavg 0.56): 45 counters identical on all four files; seconds omega +1.0 %, nat +8.8 % (spread exceeds), list −3.3 % (spread exceeds), calc_parser +0.5 %, none a result.
