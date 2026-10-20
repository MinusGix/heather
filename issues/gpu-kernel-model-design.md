---
title: Choose the GPU execution model and kernel-language level to prove against
status: open
labels: [gpu,semantics,design,research]
area: gpu
milestone: [gpu-model]
created: 2026-10-20
updated: 2026-10-20
---

Owns the roadmap's `gpu-model` milestone (`docs/roadmap.md`). The goal is a
Triton-like kernel language, or something better, whose kernels are proved
correct and efficient against a model of the GPU, as the native x86 work
does for CPU code. The design note should settle:

1. The execution model to prove against: threads, warps and blocks, the
   memory hierarchy, and which ordering and synchronisation rules are in
   scope first.
2. The level of the kernel language: tile-level (Triton) or lower, and what
   "efficient" is stated as (a cost model, not measured time).
3. What it reuses: the native program logic
   ([[native-one-program-logic]]), floating point
   ([[floating-point-formalization]]), and the ML mathematics.

No implementation until the note exists and Minus has read it.
