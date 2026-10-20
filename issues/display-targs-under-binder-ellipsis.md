---
title: A type argument that mentions a display binder still prints as `<…>`
status: open
labels: [frontend,diagnostics]
area: language
created: 2026-09-17
updated: 2026-09-17
---

`Elaborator::display_targs` recovers a declaration's monomorphized type
arguments for a diagnostic. Under a `Π`, an argument that mentions the binder
is not recovered and the whole argument list degrades to the honest ellipsis:

```heather
record Both<P, Q> { left: P, right: Q }
theorem dep<A>(P: A → Type, R: Type, h: R): (a: A) → Both<P(a), R> { h }
```

```text
error: this has type `R`, but `(x: A) -> Both<…>` is expected here
```

`Both<P(x), R>` is what the reader wants. Note the ellipsis swallows `R` too,
which *is* recoverable — the list is all-or-nothing.

## Why it is this way

[[pi-codomain-record-mismatch-panics-kernel]] made the recovery strengthen its
candidates past the display walk's binders as well as the Σ spine's, which
lands them in the `Cx` the walk started from. That is where `lower_shape`
scopes its arguments, so the re-lowering soundness check — the thing that makes
this recovery trustworthy at all — works unchanged. An argument mentioning a
walked binder has no reading in that `Cx`, so it does not strengthen.

Spelling it needs the arguments kept at the walk's *current* depth and the
re-lowering done in a correspondingly extended `Cx`. The display walk does not
build one: `Speller::under` pushes a *name*, not a context entry, because
nothing else it does needs the binder's type. The `Π` arm has the domain type
and level right there, so an extended `Cx` is constructible; what has to be
decided is whether the display walk should start carrying one, which touches
`dependent`, `instance_args` and `source_instance` as well — `instance_args`
currently just declines whenever any binder has been descended
(`names.len() != cx.names.len()`), which is the same limitation wearing a
guard.

## Acceptance

- The reproducer renders `(x: A) -> Both<P(x), R>`, with the binder's chosen
  name used in the argument.
- The re-lowering check still runs, in whatever context the arguments are
  scoped in — recovery that is not checked is not worth having, and this
  is a diagnostic reading a lowering back.
- Partial recovery, if it is taken: an argument that does not strengthen
  should cost only its own slot, not the whole list (`Both<…, R>`).
- The zero-binder path is untouched.

## Why it is not urgent

The ellipsis is this recovery's documented fallback, shared with indexed
families, value-parameterized declarations and oversized ones
([[display-inductive-type-arguments]]). The message is honest and the
declaration is still named; what is lost is the arguments. Before the panic
fix this case could not print at all.

## What it assumes from elsewhere

- **[[display-inductive-type-arguments]]** owns the recovery and its fallback.
  Assumed here: only that `<…>` is what an unrecovered argument list prints as.
- **[[pi-codomain-record-mismatch-panics-kernel]]** owns the binder-depth
  threading. Assumed here: only that arguments are strengthened back to the
  walk's starting `Cx`, which is what leaves this case unrecovered.

## Log

- 2026-09-17: Filed from the [[pi-codomain-record-mismatch-panics-kernel]] fix,
  which turned this case from a process abort into an ellipsis and stopped
  there deliberately.
