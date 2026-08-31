---
title: Make indexed-instance overlap structural
status: open
labels: [frontend,elaboration,traits,correctness]
created: 2026-08-31
updated: 2026-08-31
---

Value-generic class indices currently receive alpha-stable `#binderN`
components in the instance registry. Declaration-time overlap then splits the
rendered index key on `, ` and treats any such component as a wildcard. This is
complete for the deliberately narrow forms currently admitted by
`index_spelling`, but it makes coherence depend on a string encoding and will
not scale when index heads gain richer structural forms.

Represent instance indices as structural patterns for overlap checking while
retaining a deterministic spelling only for names and diagnostics. The
coherence decision should be alpha-invariant and independent of declaration
order.

## Acceptance

- Direct generic binders overlap every concrete term at that component.
- Alpha-renamed generic heads are the same overlap case.
- Multiple indices remain disjoint when at least one concrete component is
  disjoint.
- Any newly admitted nested index form is compared structurally rather than by
  parsing a rendered key.
- Existing indexed-class resolution and duplicate diagnostics remain stable.

## What it assumes from elsewhere

- **[[operation-indexed-classes]]** owns indexed class and instance syntax.
  Assumed here: declaration-time coherence remains the governing policy.
- **[[collection-literal-protocol]]** supplied the first value-generic index
  consumer. Assumed here: literal length remains an ordinary class index.

## Log

- 2026-08-31: Filed after value-generic indices landed for collection literals;
  the current string-wildcard check is correct for today's admitted forms but
  is the wrong extension boundary.
