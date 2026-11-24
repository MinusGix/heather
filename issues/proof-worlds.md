---
title: Scoped proof worlds: inside-to-outside internal logics (within)
status: open
labels: [frontend,syntax,elaboration,stdlib,proofs,design]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-23
updated: 2026-11-23
---

## Log

- 2026-11-23: Built v1 of scoped proof worlds (`docs/language/proof-worlds-design.md`):
  - Syntax and lowering (`crates/syntax/src/within.rs`, `parser.rs`, `try_lower.rs`): Rule-1 contextual keyword `within` for monadic worlds (`within W { … }`, auto-wrapping tail leaves in `Pointed::ret` and unwrapping tail `(<- e)`) and pointwise worlds (`within W for x [: T] { … }`, partitioning outer/inner statements and combining binds via `W::both` + `W::map`/`W::extract_with`).
  - Elaborator dispatch (`crates/elab/src/binding.rs`, `checking.rs`, `inference.rs`, plus `Type::Squash` arm in `gendefs.rs::Holes::ty` so `Trunc<A>` resolves `Bind<Trunc>`).
  - Standard library (`lib/std/core/world.hthr`): `Dne` + `Stable` (constructive excluded middle with zero axioms), `Trunc` + `SquashOut`, `Directed<I>(le)` + `Eventually<I>(le, P)` with `Nat::Le` instance.
  - Adopted in `lib/std/analysis/real_exp.hthr` (`CReal::exp_sub_lin_near`), probes in `lib/_tests/std/core/world_tests.hthr`, tree-sitter grammar updated.
