---
title: Say when a refused conversion is stuck on an opaque theorem
status: open
labels: [diagnostics,elaboration]
created: 2026-10-16
updated: 2026-10-16
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
