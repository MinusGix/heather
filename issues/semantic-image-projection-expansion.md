---
title: Keep dependent projection metadata compact in semantic module images
status: open
labels: [elaborator,caching,performance,representation,records]
area: infrastructure
created: 2026-09-03
updated: 2026-09-03
---

While factoring the linked x86 control certificate, a small three-field record
aggregating already-proved conditional decode facts caused its derived
projection material to exceed the semantic-image syntax-node rail. Removing
the aggregate was the correct local design because it duplicated evidence, but
the expansion is disproportionate to the source and makes semantic module
size difficult to predict.

Measure the declaration-to-image expansion for dependent records whose later
fields mention earlier evidence. Separate the logical record type, generated
projection/tail definitions, stored surface syntax, and serialized kernel
bindings. Then preserve references or DAG sharing across the image boundary so
that a compact source abstraction does not become a many-copy cache artifact.
Increasing the node rail without identifying the representation law is not a
fix.

## Acceptance

- A minimized record family reproduces the source-size versus image-node
  growth and attributes each generated component.
- Image inspection reports the largest declarations and generated artifacts
  when a module approaches or exceeds its configured bound.
- Repeated dependent endpoints remain referenced/shared rather than serialized
  as independent expanded trees where the semantics permits it.
- The reduced aggregate fits comfortably under the existing rail, while image
  hash determinism, corruption rejection, and restored-world equivalence stay
  green.
- Declaration-time projection cost is measured separately from persistence
  size so an improvement in one is not claimed for the other.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns the persistence format and untrusted
  restore boundary.
- **[[record-projection-defs-declaration-cost]]** owns the runtime cost of
  registering named projections; this issue owns their stored image shape.
- **[[family-types-as-code-defs]]** owns analogous sharing for generated family
  types and is a representation precedent, not a duplicate owner.
