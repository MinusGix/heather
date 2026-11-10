---
title: Re-elaborated applied-field spelling at a call receiver reaches the kernel at the wrong level
status: closed
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

## Resolution (2026-11-10)

Applied fields were not the cause. The speller writes a zero-argument
section function as a bare `Hurwitz::one<A>`, and a bare `f<A>` whose next
parameters hold a solver (the section's dictionary) filled them only at an
expected type (the bare-reference route, docs/unifier-completeness-design.md
§5.3). Inferred, as an argument whose domain was still open or as a dot
receiver, it stayed the dictionary-awaiting function. In plain user code:

```text
fn x3(f: Hurwitz<A>) → Hurwitz<A> { Hurwitz::add(Hurwitz::zero<A>, f) }   // kernel: LevelMismatch
fn z1() → A { (Hurwitz::zero<A>).coeff(0) }                              // unbound name `coeff`
```

The argument's owed comparison was recorded, but the kernel refused the
application for its levels (`Π dict → Hurwitz<A>` lives one level up)
before any conversion. `kernel_error` read only `NotConvertible` and
`HeadMismatch` as conversions, so the note was never consulted, and the
refusal came out bare.

Two changes in crates/elab/src/lib.rs:
- The `TyApp` route fills a solver prefix with nothing expected too, so
  `f<A>` is the value wherever it stands.
- `kernel_error` counts `LevelMismatch` as a conversion refusal, so a level
  disagreement is reported at the note recorded for it, and one no note
  explains is `KernelSite::Unrecorded`, which tests cannot pin.

`Speller::applied_field`'s local-receiver guard is gone: omega and ring spell
`Hurwitz::mul(one, f).coeff(n)` and `(Hurwitz::sin<A>).coeff(i)`, and
hurwitz.hthr checks. Probes: the `Sr` section at the end of
`lib/_tests/std/tactic/ring_tests.hthr`.
