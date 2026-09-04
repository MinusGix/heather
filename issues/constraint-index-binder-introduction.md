---
title: Introduce named implicit class indices with local notation in constraints
status: open
labels: [frontend,traits,notation,ergonomics,design]
created: 2026-09-04
updated: 2026-09-04
---

Implement the agreed compact-header direction (implementation pending):

```heather
theorem merge_twice<A: Mergeable(same as ≈, merge as ⊔)>(
    state, incoming: A): ...
```

It should introduce the relation/operation implicitly, with types supplied by
the class index telescope, rather than repeat their function types as explicit
arguments. Existing empty constraint slots already introduce implicit indices;
this adds control over their names and local notation.

## Agreed binder rule and implementation acceptance

- An `index as symbol` slot is a declaring occurrence, not an annotation on a
  linked reference. Preserve the existing bare-name linked-reference meaning;
  never turn an unresolved ordinary identifier into an automatic binder.
- Insert ordinary implicit index binders and the existing solver dictionary
  binder with coherent dependency ordering. Install notation over the rest of
  the declaration, including its statement. No kernel feature is needed.
- Probe multiple indices, indices depending on earlier ones, multiple classes,
  duplicate names/symbols, collision with an explicit or outer binder, and the
  explicit spelling as a fallback. Prefer rejecting ambiguous binding/capture
  over inference dependent on incidental scope changes.
- Show theorem use where the expected conclusion pins the indices, and a
  function call where it does not; the latter must request a choice rather
  than search for a default operation or relation. Keep explicit call-site
  index selection available.
- Decide whether a fresh name without notation needs a separate binder spelling;
  do not broaden bare linked slots implicitly to obtain it.
- Update the showcase only as the implementation earns each compact spelling.

## What it assumes from elsewhere

- **[[operation-indexed-classes]]** owns empty/linked/symbol slot behavior and
  implicit index inference.
- **[[binder-symbol-as-notation]]** owns notation on declaring occurrences.
  Its earlier rejection concerns decorating linked references; this follow-up
  explores a new declaring form, not silent reinterpretation of those references.
- **[[implicit-binders-in-function-types]]** owns surface implicitness handling.
- **[[relation-indexed-algebra]]** supplies the two-index theorem customer.

## Log

- 2026-09-04: Filed from the user's compact Mergeable header proposal. The
  user-authored showcase uses the explicit carrier-constraint header first,
  and records this compact form as a proposed follow-up.
- 2026-09-04: User agreed that `index as symbol` declares an implicit index while a bare name remains a reference. Implementation and detailed collision/dependency probes remain open.
