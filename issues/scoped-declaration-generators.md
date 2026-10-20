---
title: Support library-defined scoped declaration generators
status: open
labels: [metaprogramming,elaboration,design]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-09-07
updated: 2026-09-07
---

Own a general declaration expansion mechanism whose generators are Heather
functions, with runtime compilation as the first customer. A generator may
receive structured syntax, parse limited custom forms, invoke elaboration, and
construct a small module of ordinary definitions and certified instances.
No privileged recognition of every generator name is intended.

## Acceptance

- Give generators structured input with source spans and hygienic names; support
  limited custom parsing without requiring a full standalone DSL framework.
- Provide structured construction and checking of generated declarations, plus
  elaboration of fragments against expected types through the host interface.
- Check a generated module before publishing explicit exports in the caller's
  scope; keep helper names private and diagnostics traceable to source inputs.
- Distinguish generators consuming already typed Code from generators that must
  first lower syntax into a real function with extra parameters/proof arguments.
- Exercise a library-defined runtime generator that emits an ordinary Compile
  instance, without hardcoding its identifier as a compiler keyword.
- Define explicit composition inputs/outputs rather than unspecified annotation
  ordering. A generator may return evidence consumed by another generator.

## What it assumes from elsewhere

- [[host-elaboration-interface]] owns access to the active host context.
- [[runtime-compile-opt-in]] owns the compilation eligibility policy; runtime_fn
  is a provisional library name rather than a permanent reserved keyword.
- [[generators-in-the-language]] owns the broader migration.
- [[proof-carrying-function-analysis]] owns richer analysis interfaces.
