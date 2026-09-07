---
title: Certify x86 calls and concrete stack frames
status: open
labels: [compiler,x86,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Own canonical CALL/RET execution and the lowering/certification of function calls
and concrete frames. Represent the stack through RSP and byte memory, including
return addresses; do not introduce an unrelated magical stack state.

## Acceptance

- Model the supported CALL/RET forms, instruction lengths, return-address push
  and pop, and explicit memory-access and stack-capacity preconditions.
- Specify argument/result placement, clobbers, preserved live values, frame
  layout, and alignment for the initial Heather calling convention.
- Compile and certify at least two functions with nested calls and returning
  results. Test return addresses, preservation, alignment, and failure conditions.
- Explain supported spills and locals; reject unsupported frame shapes clearly.
- Keep native convention choices distinct from C interoperability adapters.

## What it assumes from elsewhere

- [[x86-64-machine-model]] owns canonical machine semantics.
- [[byte-memory-access-model]] owns memory accesses; [[finite-trapping-stack]]
  owns the separate abstract bounded-stack representation problem.
- [[x86-symbolic-fragment-layout]] owns placement and relocation of code references.
- [[runtime-compile-opt-in]] owns eligibility of transitively demanded callees.
- [[runtime-extern-c-abi]] owns foreign convention boundaries.
