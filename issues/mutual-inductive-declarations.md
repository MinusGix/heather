---
title: Mutual inductive declarations at the surface, lowered to one tagged IWf
status: open
labels: [frontend,inductives,indexed-families]
area: language
milestone: [math-metatheory]
created: 2026-10-24
updated: 2026-10-24
---

Heather can declare an indexed family (`IWf`, `docs/iwf-former-design.md`),
but not a group of mutually defined ones. The kernel route is known: one
`IWf` indexed by `Σ(tag). I_tag`. It is checked in heather-coq's rules,
including the case where the index types depend on the tag
(`probes/IwfLowering.v`, `probes/IwfLowering2.v`; doc §12.2). But
`crates/syntax` has no mutual inductive declaration, and
[[indexed-families]] leaves mutual declarations out of its scope.

The customer is [[heather-coq-port]]. heather-coq's syntax has four mutual
sorts (`ty`, `tm`, `ctx`, `lsub`), and its typing has seven mutual
judgments with 236 rules (`docs/heather-coq-port-assessment.md` §4.1).
Writing the Σ-tag encoding by hand at that size is not practical.

What it needs: a surface group of `inductive` declarations, lowered to one
tagged family. `match` and recursion are per member, and the members'
names and constructors are as written. Induction runs over the group (one
`elim_IWf`). The four testing axes of `docs/testing-generated-terms.md`
apply, and one test should use a tag-dependent index type.

## Log

- 2026-10-24: Filed from the heather-coq port assessment.
