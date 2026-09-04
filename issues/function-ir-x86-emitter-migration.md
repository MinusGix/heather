---
title: Migrate FunctionIR x86 certificates onto the structured Heather emitter
status: closed
labels: [compiler,function-ir,x86,codegen,ergonomics]
created: 2026-09-03
updated: 2026-09-03
---

The full `ControlRegion` certificate is kernel-checked and useful, but most of
its roughly thousand-line Rust generator still constructs Heather declarations
through one large interpolated source string. Small punctuation mistakes can
therefore survive Rust type checking and appear only after an expensive
semantic prefix and generated-module run. The final negative control initially
did exactly this by omitting `()` from a theorem declaration.

Migrate the FunctionIR/x86 proof path declaration by declaration onto the
shared `heather_emit` construction API. This is an engineering boundary, not a
request to bypass Heather: rendered output must continue through the ordinary
parser, elaborator, and kernel gate. Extend the emitter only for recurring
surface forms; keep `Expr::raw` visible for genuinely incremental migration.

## Acceptance

- The control-region generator no longer interpolates Heather declaration or
  proof syntax through a monolithic `format!` body.
- Names, expressions, parameters, statements, blocks, and declarations use
  typed emitter values; raw fragments are small, explicit, and inventoried.
- Existing generated-module, dishonest-edge, and golden/drift controls retain
  their semantic purpose and pass.
- Rendering is deterministic and focused snapshot failures identify the
  declaration being changed without first running the full certificate.
- The ordinary elaborator and kernel remain the trust boundary; no generator
  constructs unchecked kernel terms.

## What it assumes from elsewhere

- **[[generated-heather-direct-elaboration]]** owns whether the same emission
  IR eventually gains a non-text elaborator sink. This issue only changes how
  FunctionIR/x86 clients construct that IR.
- **[[function-ir-control-region-x86-certification]]** owns the landed proof
  and its semantic acceptance. This issue must preserve it.

## Resolution

Completed 2026-09-03. `generate_control_region` now owns one structured
`Module`. Every control-specific function and theorem is a `Declaration` with
separate generics, typed `Parameter`s, result expression, and proof `Block`;
the output is rendered once at the end. The six inputs produced by older
straight-line generators remain explicit `Module::raw` composition items and
are outside this migration's control-specific suffix.

The migration also removed copied declaration families rather than merely
transcribing them. True/false edge values, join parameters, entry placements,
operand agreement, arithmetic rewrites, selected bindings, and selected
computations are emitted from Rust tables and loops. Proposition and proof
terms not yet in the small emitter vocabulary are deliberately visible through
the two `emitted_*` constructors as one `Expr::raw` leaf per declaration; no
raw leaf owns declaration syntax or module separators.

The full Furnace control-flow rail passes after the change in 391.44s. The
honest certificate itself checks in 106.00s (57.18s kernel, 48.82s frontend),
effectively identical to the preceding 106.47s point, so the representation
change neither bypasses the checker nor hides a performance regression. The
first run caught a doubled Rust line-continuation escape at parse time before
semantic setup, which is now corrected.
