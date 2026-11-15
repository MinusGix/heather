---
title: Normalize commutative-ring identities over Nat and Int
status: closed
labels: [proofs,arithmetic,solver,mathematics,design]
created: 2026-10-10
updated: 2026-10-12
---

Commutative-ring identities over `Int` are proved by hand. In `lib/std/num/rat.hthr`
about a third of the module is monomial rearrangement: `cross_term` and
`add_respects`, `add_assoc`, `distr_monomial` and `mul_add_distr` (a
seven-factor monomial lemma), and the shuffles in `same_trans`. The pattern
that worked (docs/showcase/setoid-rationals-round.md, "Where the proof text went") is:
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

## Log

- 2026-10-12: Landed (docs/tactics/ring-normalization-design.md). Reflective, not a Rust-side
  `calc`: `lib/std/tactic/ring.hthr` holds `RingExpr`/`RingNat`, a sorted
  exponent-vector normal form and its soundness proof, checked once; the `ring`
  tactic (`crates/elab/src/ring.rs`) reifies and writes
  `RingExpr::sound(atoms, ⟦lhs⟧, ⟦rhs⟧, refl)`. `Nat` goes through its `Int`
  embedding. `ring(h, …)` combines equations with polynomial multipliers the
  tactic finds by linear algebra over candidate monomial multipliers
  (`sound_with`, the multipliers checked by the same `refl`). Defined
  propositions unfold, fields of computed records are read, convertible atoms
  are one atom.

  Acceptance: `Rat::add_assoc`, `Rat::add_respects` and `Rat::mul_add_distr`
  are one `ring` call each with their hypotheses (the `mul_int` facts, and
  `hx`/`hy` for the respect law); so are `mul_respects` and `add_neg`, and
  `same_trans` takes its scaled equation from `ring(hxy, hyz)`. `cross_term` and
  `distr_monomial` are gone. Cold, by `scripts/perf ab --source-patch`: the
  module's own declarations check faster, their kernel gate is dearer (residue:
  [[ring-certificate-kernel-cost]]), the whole file's wall is inside the
  spread. Omega was not touched: composition is a `ring` fact handed to `omega`;
  the atom-table reuse this issue assumed was not needed.

  Residue has owners: inequalities [[ring-inequalities]]; normalizing modulo a
  setoid at `Rat` itself [[semiring-ring-structure-api]]; certificate cost
  [[ring-certificate-kernel-cost]].
