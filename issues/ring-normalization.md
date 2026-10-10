---
title: Normalize commutative-ring identities over Nat and Int
status: open
labels: [proofs,arithmetic,solver,mathematics,design]
created: 2026-10-10
updated: 2026-10-10
---

Commutative-ring identities over `Int` are proved by hand. In `lib/std/rat.hthr`
about a third of the module is monomial rearrangement: `cross_term` and
`add_respects`, `add_assoc`, `distr_monomial` and `mul_add_distr` (a
seven-factor monomial lemma), and the shuffles in `same_trans`. The pattern
that worked (docs/setoid-rationals-round.md, "Where the proof text went") is:
expand by distributivity, match monomials pairwise with `mul_assoc` /
`mul_comm` / `Int::mul_shuffle`, then let `omega` do the linear part with
products as atoms. A normalizer would replace the first two steps.

Reals are the reason this matters: every regular-Cauchy modulus estimate is a
polynomial identity or inequality in several variables.

## Shape of a fix (to decide)

- **Rust-side certificate, like omega**: reify both sides into polynomials
  over atoms, normalize (sorted monomials, integer coefficients), and emit an
  ordinary `calc` of `mul_assoc`/`mul_comm`/`mul_add_distr` steps for the
  kernel. Untrusted searcher, checked output — omega's existing contract.
- **Reflective, in-language**: a `Poly` syntax, `eval`, a normalizer proved
  sound once, and `refl` on the normal forms at concrete coefficient lists
  with abstract atoms. Cheaper certificates, but the soundness proof and
  conversion cost are a round of their own.

Either should cover `Nat` as a commutative semiring and `Int` as a ring, and
compose with omega (a ring step inside an otherwise linear goal).

Acceptance: `Rat::add_assoc`, `Rat::add_respects` and `Rat::mul_add_distr`
rewritten as one-line normalizer calls (plus their hypotheses where a law needs
one), with the module's cold check no dearer.

## What it assumes from elsewhere

- **[[omega-linear-arithmetic]]** owns omega. Assumed here: only that its
  atom table can be reused for ring atoms.
