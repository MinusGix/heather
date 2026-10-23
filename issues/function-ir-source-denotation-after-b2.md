---
title: What proves a FunctionIR region means its source function after B2
status: open
labels: [native,ir,proofs,metaprogramming,design]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-21
updated: 2026-10-23
---

Today a Heather function reaches native code through
`crates/elab/src/function_ir_source.rs`. The Rust reflector reads the
elaborated body, builds a FunctionIR region, and emits a source-to-IR
theorem naming the real source function, which the kernel checks. Burn B2
(`docs/native-program-logic-design.md` §3.2) deletes "the
`function_ir_source` publication and loop generators" along with the
per-function x86 certificates. The verified lowering
([[function-ir-verified-lowering]]) proves IR to x86 once, but nothing in
the plan says what will prove, after B2, that the region the lowering
compiles is the meaning of the function the user wrote.

Found while mapping the native state for Minus (2026-10-21); filed at his
request.

## Options

1. **Keep the reflector, keep its certificate.** The Rust reflector stays
   as an untrusted producer, and the source-to-IR theorem keeps being
   emitted per function. That theorem is small, and linear in the region,
   unlike the x86 certificates B2 removes. B2's list is narrowed to exclude
   it. The cheapest option, and it leaves logic in Rust.
2. **Reflect in Heather.** A Heather metaprogram reads the elaborated body
   through the host interface's `View` (`tac-host-interface` R2) and builds
   the region together with its proof, like a tactic. This is
   [[generators-in-the-language]]'s direction and `hih-passes`'s
   milestone, and it shares its interface with tactics.
3. **The source is the IR.** Programs are written in the effectful source
   ([[native-effect-source-compiler]]), whose leaves are FunctionIR regions
   written directly or elaborated from a surface. In that case there is no
   reflection step to prove. This works for the effectful path but not for
   compiling existing pure Heather functions.

The likely answer is 1 until 2 is possible, with 3 for effectful programs.
That should be decided before B2 starts, not discovered during it.

## What it assumes from elsewhere

- **[[source-function-ir-expression-dags]]** owns the reflector's coverage.
- **[[in-language-certificate-emission]]** and
  **[[generators-in-the-language]]** own moving emission into Heather.
- **[[native-first-compiled-program]]** owns B2's timing.

## Log

- 2026-10-21: From `docs/native-effect-source-design.md` §9: for effectful programs the answer is option 3 (the program is the effectful source, written or elaborated; nothing is reflected). For pure functions, the bounded loop proposed there for FunctionIR is what lets reflected structural recursion stay total; "1 now, 2 when the host `View` exists" stands.
- 2026-10-23: Option 1 got cheaper in [[function-ir-verified-lowering]] round 4. On the verified path the reflected program is tied to its source by one equation, `program_eval(program, f, args) = source(args)` over open words, proved by `refl` against the total evaluator. No per-function source-to-IR certificate is generated. The reflector stays untrusted Rust. Option 2 would build the same program in Heather and keep the same `refl` equation.
