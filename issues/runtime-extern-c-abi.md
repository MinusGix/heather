---
title: Define explicit C ABI imports and runtime exports
status: open
labels: [compiler,abi,design]
area: heather-in-heather
created: 2026-09-07
updated: 2026-11-11
milestone: [nh-library]
---

## Scope

Own explicit foreign C ABI boundaries while allowing Heather to choose its own
native calling convention. The existing bootstrap SysV callable export does not
establish C as the eventual default for Heather-to-Heather calls.

A spelling such as `runtime_fn(abi="C")` could select an exported function's ABI,
but remains provisional. An imported foreign declaration with no Heather body
needs its own declaration and contract design; an export annotation alone does
not solve imports.

## Acceptance

- Distinguish imported foreign symbols, exported Heather definitions, and ordinary
  native functions, with explicit target/platform-specific ABI metadata.
- Start with a bounded x86-64 SysV integer-signature subset. Specify registers,
  stack alignment, caller/callee clobbers, argument/result representation, and
  adapter obligations; diagnose unsupported signatures and ABI mismatches.
- Integrate symbol resolution and ABI metadata with certificates and artifact
  identity. Successful linking is not proof of an external function's behavior.
- Expose assumptions/contracts for foreign behavior and memory effects clearly.
- Test a supported import and export against C, plus mismatch/unsupported cases.
- Scope out varargs, callbacks, TLS, and aggregate passing until explicitly
  modeled. Keep native convention design free of accidental C defaults.

## What it assumes from elsewhere

- [[named-abi-contracts]] owns the named convention specification and the distinction
  between checked conformance and explicitly assumed foreign conformance.
- [[x86-call-memory-footprints]] owns frame/protected-memory obligations; imported
  functions additionally need their own pointer and shared-memory effects.
- [[runtime-compile-opt-in]] owns instance eligibility and the marker mechanism.
- [[x86-calls-stack-frames]] owns concrete calling and frame semantics.
- [[x86-symbolic-fragment-layout]] owns symbolic references and relocations.
- [[x86-native-export]] owns the existing bootstrap callable export.
- [[foreign-binary-contracts]] (speculative, 2026-11-11) would discharge an
  import's assumed contract against the callee's machine code; its round F0 is
  the assumed import with axiom provenance that this issue's imports need.
