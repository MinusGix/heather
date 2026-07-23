---
title: Certifying generator for Compile instances (runtime_func)
status: open
labels: [compiler, metaprogramming]
blocked-by: [end-to-end-compile-instance]
created: 2026-07-22
updated: 2026-07-22
---

The `runtime_func`-style generator: intensionally analyze boxed function code
and emit a `Compile` instance *plus its equiv proof*. Because each output
carries its own certificate (checked by the kernel like any proof), the
generator itself needs no verification — it can be heuristic, incomplete, or
user-written, affecting only *which* functions compile, never soundness.
Protect this property as the design evolves.

Surface form TBD: possibly not a named wrapper but a macro over
`eval(generate(box f))`.
