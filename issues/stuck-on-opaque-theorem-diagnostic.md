---
title: Say when a refused conversion is stuck on an opaque theorem
status: closed
labels: [diagnostics,elaboration]
created: 2026-10-16
updated: 2026-10-19
---

When a `refl` or a conversion is refused because the reduction it needed is
stuck on an opaque `theorem`, the message does not say so:

```
error: the kernel rejected `add_zero_start`: NotConvertible. `refl` needs both sides to be definitionally equal, but `add_zero(one, 3).witness` and `7` are not
```

Here `CReal::add_zero` was a `theorem`, so `.witness` of it can never
reduce. Nothing in the message says which global blocked the reduction or
that it was opaque by design. A writer with a `fn` background reads it as
"the modulus is wrong". Found in the regular Cauchy reals round
([[regular-cauchy-reals]]), where every data-carrying proof had to become a
`fn`.

Wanted: when the stuck head of either side (after whnf) is an elimination
whose scrutinee is headed by a `theorem` or `axiom` global, the note names
it: "`CReal::add_zero` is a theorem, so it never unfolds; …". The note
should point at the current way to compute with a proof (a `fn`, or the
unfolding form [[theorem-witness-unfolding]] lands).

Since [[theorem-witness-unfolding]] landed, a theorem whose statement
carries data is opened by such a projection, so the case left is a theorem
whose statement the classifier judged data-free, or an `axiom`
(`check_reports_mismatch.rs`'s projection fixture is an axiom for this
reason). The note should say which.

Acceptance: a test in `crates/elab/tests/check_reports_mismatch.rs` with an
axiom-built `Exists` projected under `refl`. A control does the same with
a `fn` and checks.

## Log

- 2026-10-19: LANDED. A refused conversion whose side, after whnf, is an
  elimination chain (projection, `match`, recursor, `J`, through any
  applications) headed by a named body-less global with no sealed proof
  now says why: "`ex` is an axiom, so it has no proof to unfold and what is
  stuck on it never computes", or "`ex` is a theorem whose statement was not
  judged to carry data, so its proof is not kept and never unfolds; to
  compute with what it builds, declare it as a `fn`". A bare call of such a
  global is not named (a value, not a stuck reduction), and a theorem with a
  sealed proof is never named (the elimination opens it; meeting one stuck
  means the note's budget ran out). Both the `refl` note and the checking
  note carry it; the checking note reads the endpoints of the two types when
  they are equations, which is the projection fixture's shape
  (`mk_w().pres` at `0 = 0` now names `mk_w`). Error path only: a whnf per
  side at the `refl` note's budget, after the probe has decided
  `NotConvertible`. `Elaborator::opaque_stuck_note`, `eliminated_global` in
  `crates/elab/src/lib.rs`. Tests in `check_reports_mismatch.rs`: an axiom
  projected under `refl`, a theorem whose statement decodes through a
  `match` on its parameter (data-free to the sealing test), and the `fn`
  control, accepted and, with a false equation, naming nothing.
  Noticed on the way: a nullary call spells without its parentheses
  (`(ex).witness` for `ex().witness`), since a bare `GlobalTm` displays as
  its name; the tests use a one-parameter axiom ([[nullary-call-spells-without-parens]]).
