---
title: omega spells a context atom without an implicit it needs, and its certificate fails
status: closed
labels: [omega,proofs,elaboration]
created: 2026-09-25
updated: 2026-09-26
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
- 2026-09-25: The repro above now checks: [[omega-relevant-facts-only]] leaves out the
  fact, since the goal is not over its atom. A goal that uses the atom still
  fails the same way, for example
  `fact: BitVec::ofNat(5, n := 64).toNat() = n ⊢ BitVec::ofNat(5, n := 64).toNat() < 20`.
  The spelling itself remains this issue's.
- 2026-09-26: Fixed in the speller (`display.rs`, `Speller::call`). When it spells for
  re-parsing, it keeps an implicit argument that no later explicit parameter's
  domain mentions: `BitVec::ofNat(5, n := 64)`. A leading type parameter the
  call does not determine is written in `<…>` (`empty<Nat>()`). Named arguments
  follow the positional ones. `bv_omega` needed this at its first `ofNat`
  ([[bitvec-nat-lifting-tactic]]). Acceptance: `crates/elab/tests/bv_omega.rs`,
  `respelled_atoms_elaborate` (the one-liner, the goal-uses-the-atom case, a
  type argument, and a false bound over the respelled atom that is still
  refused).
