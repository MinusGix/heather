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

## Log

- 2026-10-01: The stream filter landed (docs/native-stream-filter-design.md): its claim is read_filter_runs over filter_events, and filter_prints says stdout is spec(stdin) — the observable this logic must reproduce.
- 2026-10-07: An incremental step toward this logic for straight code: [[native-straight-code-triples]].
- 2026-10-20: 2026-10-20: Designed in docs/native-program-logic-design.md (answers the three questions in §1): specs as coalgebras over a Linux call/answer container, the judgment Sim bridged to LinuxRuns, one computed Wp over Asm items with Syscall and Proved items, and loop_at measured by the history. The work is five rounds with owners: [[native-linux-spec]], [[native-one-wp]], [[native-loop-rule]], [[native-filter-on-program-logic]], [[native-retire-execution-shapes]]; the tactic is [[wp-obligation-tactic]] and question 3 moved to [[ir-v1-retirement]]. Closed: the design is this issue's scope.
