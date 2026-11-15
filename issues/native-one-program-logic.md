---
title: One program logic for native code, designed to meet interaction trees
status: closed
labels: [native,x86,ir,semantics,design]
area: heather-in-heather
milestone: [hih-program-logic, it-native]
created: 2026-10-01
updated: 2026-10-20
---

The native stack says "this code runs" five ways: `ExecuteBlock`,
`ExecuteStructured`, `ExecuteAccess`, fetched steps and Linux steps
(`docs/archive/native-architecture-review.md` §2.4). Nothing above a single fetched
step can hold a store or a syscall, so every loop with one is a hand
induction in a process library. The review's "not proposed now" names the end
state: one effectful code tree (stores, syscalls, labelled edges) and one
program logic over the Linux trace, proved once. Beside that there are two
IRs: `ir_v1` with the certifying generator (about 3k lines of library) and
FunctionIR, which the x86 path uses.

This issue owns the design of that unification. It is to be designed now and
built after the interaction-tree groundwork, because the program logic's
postcondition should be stated over traces such that "this code refines the
interaction tree t" comes out later as a lemma, not a re-founding. Questions:

1. One step relation with derived rules for the current five shapes, or a
   structured code tree with Hoare rules? Mind the kernel's depth and `let`
   limits that made R1 → R4 the incremental route.
2. Do processes become FunctionIR regions with state edges (RVSDG state edges
   are uniqueness threading, the first leaning of [[effects-direction]])
   instead of hand-written x86 libraries?
3. Is `ir_v1`/certgen retired onto FunctionIR, or kept as the Nat-level
   source IR?

## What it assumes from elsewhere

- **[[interaction-trees-container-model]]** owns the container-event trees.
  Assumed here: only that read/write/exit events are a container
  (`Cmd`/`Resp`), so a Linux trace is a finite trace of such a tree.
- **[[effects-direction]]** owns the effects verdict. This issue supplies an
  IR customer and does not decide it.
- **[[native-loop-emitting-stores]]** owns the stream-filter program shape,
  whose `stdout = spec(stdin)` claim this logic must reproduce.

## Log

- 2026-10-01: The stream filter landed (docs/archive/native-stream-filter-design.md): its claim is read_filter_runs over filter_events, and filter_prints says stdout is spec(stdin) — the observable this logic must reproduce.
- 2026-10-07: An incremental step toward this logic for straight code: [[native-straight-code-triples]].
- 2026-10-21: Designed in docs/native-program-logic-design.md (§1 answers the three questions; revised after Minus's review): native code is rebuilt on interaction trees as a compiler from an effectful source proved correct once, with the program logic (`Sim` against a tree, one computed `Wp`, `loop_at`) as the target-side tools. The hand-proved process stack burns first ([[native-burn-process-stack]]); the rounds are [[native-linux-spec]], [[native-one-wp]], [[native-loop-rule]], [[native-effect-source-compiler]], [[function-ir-verified-lowering]], [[native-first-compiled-program]]; question 3 is [[ir-v1-retirement]]. Closed: the design is this issue's scope.
