---
title: A forgotten self marker on a type-owned member masquerades as failed generic inference
status: closed
labels: [frontend,elaboration,diagnostics,ergonomics]
created: 2026-09-21
updated: 2026-09-24
---

Found while moving the parser library's helpers into type-owned namespaces.
This declaration forgets that its receiver is the second explicit parameter:

```heather
fn Failure::error_view<T>(
    source: List<T>,
    error: Failure<T>(source),
) -> ErrorView { ... }

// e: Failure<T>(source)
e.error_view(source)
```

The receiver's type successfully selects `Failure::error_view`, but the absence
of a `self` marker makes `subject_index` use its intentional default, the first
explicit parameter. The call is therefore elaborated approximately as
`Failure::error_view(e, source)`. Matching `e: Failure<T>(source)` against the
first parameter's `List<?T>` does not solve the implicit type argument, and the
eventual message reports:

```text
cannot infer the type argument `T` of `Failure::error_view` here — no argument's
type mentions it; write `Failure::error_view<…>(…)` to give the type arguments
```

That diagnosis is locally true of the failed application schedule but misses
the cause the author can act on. Supplying `<T>` would only expose the swapped
argument types. The intended declaration is:

```heather
fn Failure::error_view<T>(
    source: List<T>,
    self error: Failure<T>(source),
) -> ErrorView { ... }
```

This is not an implicit-inference completeness problem. Receiver lookup already
inferred enough about `e` to choose the owner's namespace; the application then
put that receiver in the position the declaration requested by omission.

## Desired diagnostic

When a dot call selects a type-owned member, the member has no `self` marker,
and application fails after defaulting the receiver to explicit parameter zero,
look for the narrow mistake above. If the receiver is incompatible with the
default subject parameter but is compatible with exactly one later explicit
parameter, report that parameter and suggest marking it `self`:

```text
`error_view` treats its first parameter `source` as the receiver because the
declaration has no `self` marker, but this receiver has the type expected by
`error`; did you mean `self error: Failure<T>(source)`?
```

The check may instead live as a declaration lint for type-owned members if it
can make the same claim without speculative use-site elaboration: no marked
subject, an owner-incompatible first explicit parameter, and exactly one later
owner-compatible parameter. It must not turn every unmarked type-owned member
into an error. Default-subject-first is deliberate, and a namespace may also
contain declarations intended primarily for qualified calls.

## Acceptance

- Reproduce the `Failure::error_view` shape with an implicit type argument and
  a dependent value parameter before the intended receiver.
- At `e.error_view(source)`, point to the missing `self` marker rather than
  recommending explicit type arguments as the primary fix.
- Keep an unmarked member whose receiver really is its first explicit parameter
  silent and working.
- Do not issue this suggestion for an ordinary global call, a qualified call,
  or a member where no unique later parameter is compatible with the receiver.
- Preserve the existing error as fallback when the receiver-position
  hypothesis cannot be established cheaply and unambiguously.
- Test a non-generic member too: this is receiver placement, not a special case
  for the type-argument diagnostic that happened to reveal it.

## Related

- **[[method-receiver-position]]** owns the `self` marker and the deliberate
  first-explicit-parameter default.
- **[[type-owned-members-receiver-slice]]** owns receiver-directed namespace
  selection. Its known signature-validation limit is why this declaration is
  accepted and the mistake currently survives until the call.

## Log

- 2026-09-21: Filed from the parser stdlib namespace migration. The concrete
  failure first looked like a question about generic placement and inference;
  tracing method desugaring showed that the receiver had been inserted into the
  unmarked first parameter instead.
- 2026-09-24: 2026-09-24: Landed with the namespace round (docs/receiver-member-resolution-design.md; §7 lists what was built and where it deviated). Full suite 2939 passed.
