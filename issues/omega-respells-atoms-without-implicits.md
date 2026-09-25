---
title: omega spells a context atom without an implicit it needs, and its certificate fails
status: open
labels: [omega,proofs,elaboration]
created: 2026-09-25
updated: 2026-09-25
---

## Scope

`omega` rebuilds its certificate as source, spelling every atom of every
reflected hypothesis. An atom whose term has an implicit argument the
elaborator can't infer from the spelling alone is spelled without it, and
the certificate then fails to elaborate. It fails even when the goal doesn't
mention that atom at all:

```text
theorem respell(n: Nat, fact: BitVec::ofNat(5, n := 64).toNat() = 5, small: n < 10): n < 20 { omega }
error: could not infer the implicit argument `n` of `bitvec::BitVec::ofNat`
```

Found writing `lib/decimal_line.hthr` and `lib/elf64_read_print.hthr`
(2026-09-25). The workaround there is ordering: prove the Nat facts before
any bitvector fact is in scope, or in a lemma of their own.

Two fixes are possible. The speller could emit an implicit it can't show is
inferable (`display.rs`'s `spell_term_source`). Or omega could leave out
hypotheses whose atoms the goal's constraint system never uses. The first is
the general one: other generators spell terms the same way.

## Acceptance

- The one-liner above checks.
- A negative control shows that an atom the certificate does use is still
  spelled so that it elaborates to the same term.

## Log

- 2026-09-25: Found alongside a second defect, fixed the same day
  (`omega_cert.rs`, `coeffs_source`). A GCD-divided row was rendered with
  `Coeffs`' trailing zeros dropped, while the rows it is compared with keep one
  entry per atom. `dot` of the shorter row isn't definitionally equal once a
  dropped atom is neutral (`0 * x` doesn't reduce), so the kernel refused
  certificates such as `n.div(10).div(10) = n.div(100)` and `v + v = 2 * v` in
  a context with other atoms. Rows are now padded to the atom count.
