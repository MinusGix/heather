---
title: Mutual inductive declarations at the surface, lowered to one tagged IWf
status: closed
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
- 2026-10-24: Done, design in `docs/mutual-inductive-design.md`. A run of
  `inductive`s that mention one another is a group, lowered to one `IWf`
  indexed by a generated sum of the members' indices (`D#members`), not
  `Σ(tag). I_tag`: the sum says the tag dependence by construction, so the
  index types need no codes (§2 there). Each member is a view: `match` on it
  inverts on the member, per level, so other members' arms and impossible
  arms are neither written nor accepted. A cycle of measure-free `fn`s or
  `theorem`s over the members is one structural recursion, one `elim_IWf`
  (§6). Tests: `crates/elab/tests/mutual_inductive.rs`, including members
  indexed by a declared type and by `Nat`. Follow-up:
  [[rewrite-by-ih-after-unfolding]].
