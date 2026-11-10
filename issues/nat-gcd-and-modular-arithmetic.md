---
title: "gcd, Bezout, coprimality, primes and the Chinese remainder theorem"
status: open
labels: [stdlib,mathematics,number-theory]
area: mathematics
milestone: [math-number-theory]
created: 2026-11-10
updated: 2026-11-10
---

Area 4 of the 2026-11-10 ranking.

`lib/` has no `gcd`: `rat.hthr` says so on purpose (rationals are never
reduced). `nat.hthr` and `int.hthr` have `ModEq` and divisibility (omega
reads them) and nothing above.

## Scope

- `Nat::gcd` by Euclid with its specification (greatest common divisor
  in the divisibility order), `lcm`, and extended Euclid giving Bezout
  coefficients at `Int`. Facts go in `nat.hthr`/`int.hthr` or a module
  beside them that only they own (project rule: a type's facts live in
  its file; [[theory-modules-after-their-tactics]] owns the split that
  lets these proofs use `omega` and `ring`).
- Coprimality, Euclid's lemma, cancellation in `ModEq` by a coprime
  factor, modular inverses computed from Bezout.
- `Prime` with a decidable test by trial division, and uniqueness of
  factorisation up to `Perm`.
- The Chinese remainder theorem for two coprime moduli, with the
  witness computed.
- Fermat's little theorem and Euler's theorem can wait for
  [[integers-mod-n]], where they are statements about a group.

## Done when

A closed `gcd` evaluates by `refl`, the inverse of `a` mod `m` is a
function with its law, and CRT is stated with a computed witness.

## What it assumes from elsewhere

- **[[univariate-polynomials]]** is the same milestone's independent
  round. Assumed here: nothing; polynomial gcd is its own later step.
