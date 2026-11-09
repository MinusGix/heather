---
title: Separation algebras (PCMs) for exclusive ownership
status: open
labels: [algebra,native,ownership]
area: mathematics
milestone: [nh-ownership]
created: 2026-11-09
updated: 2026-11-09
---

Memory framing does not need a separation algebra: memory is a total
function and stores keep everything outside their span, so locality of a
predicate to a footprint (dynamic frames) is enough, and
[[address-interval-sets]] with [[state-location-and-frame-kit]] give it.
Ownership does: the ownership setup wants "this function holds `xs`
exclusively" as a resource that composes, splits when a borrow is taken and
recombines when it ends. `docs/native-mathematics-survey.md` §7; survey
rank 7. File-now, build-with-the-ownership-round.

## Scope

- A partial commutative monoid class (composition defined on compatible
  elements; commutative, associative, unit), with products and pointwise
  lifting.
- Exclusive ownership of footprints as the first instance; shared read
  access as the second when a borrow needs it. No fractions until something
  is concurrent.
- A separating conjunction on predicates over a PCM and its frame theorem.

## Done when

The ownership setup's soundness theorem states uniqueness through the PCM,
and an arena allocation hands out a footprint the caller owns exclusively.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the setup and its judgment.
  Assumed here: only that it needs composable exclusive ownership.
- **[[address-interval-sets]]** owns footprints as values.
