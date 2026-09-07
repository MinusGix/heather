---
title: Require explicit Compile instances or runtime derivation markers
status: open
labels: [compiler,frontend,metaprogramming]
created: 2026-09-07
updated: 2026-09-07
---

## Decision

Runtime compilation requires a `Compile` instance. A user may write the instance
or explicitly mark a function to synthesize one. Unmarked functions do not gain
an instance through an automatic backend fallback. This supersedes the older
“annotate nothing” default-derivation proposal in [[compile-typeclass-design]].

`runtime_fn`, `run_fn`, and `rfn` are candidate spellings; naming and final syntax
remain open. The marker requests an ordinary checked instance, not a special
logical execution mode or a privileged bypass of the compiler contract.

## Acceptance

- Route entry and transitively demanded callee compilation through instance
  discovery. Reject missing instances with an actionable diagnostic.
- Accept a valid handwritten instance without a marker; make the marker generate
  the equivalent checked instance through the normal synthesis/resolution path.
- Update `examples/x86-native/mix.hthr` to opt in explicitly and retain both
  native export and standalone executable demonstrations.
- Test unmarked rejection, marked success, handwritten-instance success,
  callee eligibility, invalid certificates, and ambiguous manual/derived cases.
- Preserve source-definition/certificate coupling and invalidate stale artifacts
  after relevant source, marker, target, or ABI changes.
- Choose and document spelling separately from the already settled requirement
  for explicit opt-in. Do not silently retain implicit derivation as a fallback.

## What it assumes from elsewhere

- [[compile-typeclass-design]] owns the Compile contract and coherence policy.
- [[source-to-function-ir-certification]] owns the current source-to-FunctionIR
  certificate route; do not route it through legacy IR just to package instances.
- [[runtime-extern-c-abi]] owns ABI selection and foreign boundary semantics.
