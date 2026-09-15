---
title: Compare cached parser cursors on nested and long-input workloads
status: open
labels: [stdlib,parsing,performance,proofs]
created: 2026-09-14
updated: 2026-09-15
---

## Problem

The first parser library derives the remainder with `drop(source,offset)`.
This can rescan prefixes. Its depth-1/2/4/8 acceptance sweep has approximately
linear serialized checked-delta growth, but superlinear evaluator work for
nested parentheses. `CachedCursor` establishes a coherent alternative in the
prototype; it does not yet replace the parser's input representation.

## Scope and protocol

Compare derived and cached representations using the existing checked
composition/parenthesis fixtures, extended with long flat input and repeated
consumption. Run serially with `set_kernel_workers(1)`, exclude library warmup,
and record deterministic evaluator counters and checked-delta bytes separately
from elapsed time. Delta bytes include syntax/registry metadata, so identify
them as a growth proxy rather than exact proof-node counts. Use `scripts/test`
for these frontend acceptance fixtures; isolate any kernel benchmark gate.

Prove that cache initialization, advancement, rebasing and backtracking retain
source identity and suffix coherence. Measure construction/checking of those
proofs as well as suffix access. Do not assume erased proofs or native runtime
behavior that the chosen representation has not established.

## Acceptance

- Comparable checked outputs and failure observations for both representations.
- Open-element coherence laws and refusal of fabricated suffixes/source swaps.
- Depth and length series with a documented representation choice; no baseline
  rewrite that hides a regression.
- Any optimized interface retains dependent bind and progress certificates.

## What it assumes from elsewhere

- [[parser-combinator-library]] owns the checked initial library; this issue
  owns the representation/performance comparison and any resulting migration.

## Log

- 2026-09-15: The depth sweep now reuses the calculator acceptance image in `showcase_calculator.rs` instead of rebuilding it in `parser_library.rs`. Its generated cases remain at depths 1/2/4/8. [[parser-certified-composition-cost]] separately owns semantic-evidence checking cost exposed by grammar soundness.
