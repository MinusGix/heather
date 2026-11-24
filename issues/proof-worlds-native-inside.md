---
title: Native inside syntax for proof worlds: classical if in Dne, require in Eventually, direct Squash
status: closed
labels: [frontend,syntax,elaboration,stdlib,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-24
updated: 2026-11-24
closed: 2026-11-24
---

Follow-up to [[proof-worlds]] (`docs/language/proof-worlds-design.md`) giving
each built-in proof world native inside syntax:

1. **Classical `if [h:] P { … } else { … }` inside `within Dne`:** tries
   decidable `if` (`Decide<P>` / `Bool`) first; when that fails in a `Dne<_>`
   goal and `P` is a valid proposition type, falls back constructively to
   `Bind::seq(Dne::em(P), λ #dne_em => match #dne_em { Inl(h) => …, Inr(h) => … })`
   with zero axioms (`crates/elab/src/binding.rs`, `checking.rs`).
2. **`require [h:] P;` inside `within Eventually for x`:** contextual statement
   lowering to `let h <- W::synth(λ x => P);`, backed by `DefaultOrder<I>`,
   `Eventually::synth`, and record-keyed `evidence theorem` resolution
   (`crates/syntax/src/{parser.rs,within.rs}`, `crates/elab/src/resolve.rs`,
   `lib/std/core/world.hthr`, `lib/std/analysis/real_exp.hthr`).
3. **Direct `within Squash { let h <- q; … }` on primitive `∥A∥`:** primitive
   `λ (A: Type) => ∥A∥` carrier in `traits.rs` and `gendefs.rs` (`constructor_spelling`),
   with `Bind<λ (A: Type) => ∥A∥>`, `Pointed<λ (A: Type) => ∥A∥>`, and
   `Squash::exit` in `lib/std/core/world.hthr` — no `Trunc::of` wrapper required.

Verified in `lib/_tests/std/core/world_tests.hthr` and
`lib/std/analysis/real_exp.hthr` with `--review --deny-axioms`.



