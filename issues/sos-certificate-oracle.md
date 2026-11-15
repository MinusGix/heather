---
title: Suggest sum-of-squares hints for nlinarith by an offline SDP oracle
status: open
labels: [tactics,arith,solver]
area: tactics
created: 2026-10-28
updated: 2026-10-28
---

`nlinarith` finds only the squares that the problem shows, or that a hint
names (docs/tactics/nonlinear-arithmetic-design.md §4). A Positivstellensatz search
by semidefinite programming finds squares of arbitrary polynomials up to a
degree. Examples are `(x² − y)² + x²` for `x⁴ − 2x²y + y² + x²`, and
certificates with many terms that nobody would write by hand. This is Coq's
`psatz`, HOL Light's `REAL_SOS` and Isabelle's `sos`.

The shape is fixed by design §5, and it differs from those tools in one
respect: **the solver never runs in the gate.** A command
`heather suggest-squares <file> --only <decl>` reads the goal as `nlinarith`
does, poses the SDP over the monomial basis, solves it numerically, rounds to
rationals, checks the identity exactly, and prints the
`nlinarith(…, sq_nonneg(t₁), …)` text to paste. The library then replays
ordinary source deterministically on every machine, which is the property of
Isabelle's stored `sos` certificates and of `polyrith`'s
`linear_combination` output. The solver is a crate above the kernel (a
pure-Rust conic solver such as Clarabel) or an external CSDP process. Either
is untrusted, and neither enters the trusted path.

Not started: no library goal needs it yet. The trigger is the first goal
that `nlinarith` with a short hint list refuses, or one whose hint list is
long enough that finding it by hand is the work.

## What it assumes from elsewhere

- **[[nlinarith-products-of-facts]]** owns the certificate and the hint
  spelling. Assumed here: a hint `sq_nonneg(t)` and a product
  `mul_nonneg(h₁, h₂)` are facts that `nlinarith` takes.

## Log

- 2026-11-05: gardener: cites a file it shares with [[interval-variable-boxes]] (`docs/tactics/nonlinear-arithmetic-design.md`); [[linarith-simplex-search]] (`docs/tactics/nonlinear-arithmetic-design.md`).
