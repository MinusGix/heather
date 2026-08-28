---
title: Reduce residual stored application annotation conversion cost
status: open
labels: [kernel,conversion,performance,representation]
created: 2026-08-28
updated: 2026-08-28
---

Restoring the annotation-directed neutral application rule fixed
[[generated-term-oracle-controls-not-convertible]], but serious generated code
still compares tens of thousands of stored dependent Π components. The rule is
semantically required; this issue owns making its representation and
instantiation cheaper without returning to the incomplete left-inferred Π
shortcut.

Feature-gated application metrics on the x86 base module report 48,588 stored
component checks (24,294 domains and codomains). Existing scoped identity
settled 6,704 (13.8%). Pointwise environment-value identity for closures that
share one syntax body safely raises that to 12,161 (25.0%), leaving 5,147
shared-body/different-value-environment misses and 31,280 other misses. The
fold/tabulate oracle controls have zero identity hits: their 20 and 114
component checks respectively remain full comparisons, as correctness
requires.

## Acceptance

- Attribute the residual between annotation syntax size, closure
  instantiation/allocation, and genuinely repeated conversion before adding a
  cache or broader equality predicate.
- Preserve the annotation-directed ch. 06 rule and all generated oracle
  controls under their existing fuel.
- Any identity shortcut must be scoped and constructive: no persistent raw
  pointer keys, address ordering, speculative fallback, or fuel rollback.
- Measure the isolated x86 module/kernel phases and the complete consolidated
  suite; do not use the former five-module aggregate timeout as a performance
  oracle.
- If the residual requires a common/paired neutral type rather than a
  representation improvement, write that kernel design separately before
  implementation.

## What it assumes from elsewhere

- **[[generated-term-oracle-controls-not-convertible]]** establishes why the
  stored Π spelling cannot simply be discarded.
- **[[bitvec-closed-reduction-cost]]** owns the remaining closed generated
  carry/unary arithmetic costs, not generic application annotations.

## Log

- 2026-08-28: Filed from the first annotation-metrics round. A warmed A/B of
  pointwise environment-value identity improved the consolidated x86 suite
  from 115.11 s to 105.38 s and the base module from 46.24 s / 24.00 s kernel
  to 43.13 s / 22.49 s kernel. A confirmation measured 43.44 s / 22.42 s and
  110.18 s for the noisier complete suite. Kernel (299), BitVec (7), IR fuel,
  and fold/tabulate/map/nth controls remain green.
