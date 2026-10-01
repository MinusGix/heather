---
title: One program logic for native code, designed to meet interaction trees
status: open
labels: [native,x86,ir,semantics,design]
created: 2026-10-01
updated: 2026-10-01
---

The native stack says "this code runs" five ways: `ExecuteBlock`,
`ExecuteStructured`, `ExecuteAccess`, fetched steps and Linux steps
(`docs/native-architecture-review.md` §2.4). Nothing above a single fetched
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
