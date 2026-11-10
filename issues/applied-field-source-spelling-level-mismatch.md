---
title: Re-elaborated applied-field spelling at a call receiver reaches the kernel at the wrong level
status: open
labels: [elaborator,spelling,gate-only-refusal]
area: language
created: 2026-11-10
updated: 2026-11-10
---

`Speller::applied_field` (crates/elab/src/display.rs,
[[omega-applied-field-atom]]) spells a function-valued field applied,
`r.f(a)`. For a *source* spelling (`qualified`, which omega, ring and
generated annotations re-elaborate) it is limited to a receiver that is a
local, because two wider receivers went wrong when it was not:

- **A kernel `LevelMismatch` with no elaborator error.** With any receiver
  allowed, `Hurwitz::one_mul_at` (lib/std/algebra/hurwitz.hthr:320, the
  `match n` over `Hurwitz::mul(Hurwitz::one(), f).coeff(n)`) was refused by
  the kernel at `one_mul_at#aux0` with `LevelMismatch`. Some consumer
  re-elaborated a spelling such as `Hurwitz::mul(one, f).coeff(n)` to a term
  at the wrong universe level and accepted it; the gate caught it. That is
  an elaborator route placing a term it did not check, the
  [[unrecorded-kernel-refusals]] class, and is the real defect here.
- **A receiver with type arguments.** `ring`'s atom list spelled
  `(hurwitz::Hurwitz::sin<A>).coeff(i)` (hurwitz.hthr:472), which the
  atom-list elaboration refused as `unbound name coeff`.

Repro: drop the `self.qualified && !matches!(&**receiver, Term::Var(_))`
guard in `applied_field` and check hurwitz.hthr.

## Done when

The consumer that accepts the wrong level is found and checks what it
places, and `applied_field`'s source spellings take any receiver
`field_read` would (or the narrower rule is justified here).
