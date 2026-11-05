---
title: Give compiled procedures target contracts derived from their source contracts
status: open
labels: [native,proofs,design]
area: heather-in-heather
created: 2026-10-28
updated: 2026-11-01
milestone: [nh-procedures]
---

When the effectful source gains procedures that make calls (a later `Stmt`
constructor denoting by `mrec`, `docs/native-effect-source-design.md` §9;
deferred in `docs/native-real-programs-plan.md` §7), each compiled
procedure needs a target contract that other compiled code can rely on.
Today nothing needs one: tools are closed programs with procedures inlined
at build, and `native_compile_correct`'s `SimProgram` plus refinement says
everything a client can observe. Abate et al.'s WP-preservation paper
(`docs/wp-preserving-compilation-survey.md` §4) shows the shape the
contract should take, proved once in Rocq/Iris for an IMP→ASM compiler.
This issue records that shape so the procedures round starts from it.

## Scope

- **Derived, never proved per procedure.** A procedure's `Callee` contract
  (`lib/std/os/linux/linux_x86_64_wp.hthr`) is an instance of
  `Stmt::emit_runs` for its body, read through the correspondence. This is
  the paper's Theorem 2, and the same move as the pure `Proved` contract
  being `compiled_returns`.
- **A per-slot footprint.** `Target::Placed` relates the whole `Env` to the
  whole data region. A procedure's contract owns only the slots and
  buffers it uses (the paper's `Cell(x)`), with a relational frame: the
  region's other bytes are unchanged. Price the cost of the extra conjunct
  in every `goes_*` rule before committing to it.
- **Scoped locals.** The caller lends its locals at known values and gets
  them back unchanged except the result slot (`Call-Scoped`, paper
  Appendix C.2). Here this comes from a real frame per activation, not
  from the paper's resolver save and restore.
- **A clobber set per procedure.** `Callee::post` relates the states, so it
  names the registers that survive, unlike the paper's link-wide register
  pool (its stated limitation).
- **Linking.** Mutually recursive procedures verified against each other's
  contracts give a linked program's `SimProgram` (the paper's Theorem 3
  item 2, by Löb). Here it is by induction on fuel. First question: does
  `mrec` over the fuelled `Program` spend fuel per call?
- **Control.** The paper's shared counter (§6.4): two procedures that call
  each other until a shared word reaches zero, with the word handed across
  each call. Add a negative control, a callee that writes a caller slot
  outside its footprint, refused.

## What it assumes from elsewhere

- **[[native-effect-source-compiler]]** owns `Stmt::emit_runs` and
  `Target::Placed`. Assumed here: only that a statement's claim stays in
  continuation form.
- **[[wp-callee-from-lowered-function]]** owns turning a lowered
  function's theorem into a `Callee`. This issue is the effectful case.
- **[[wp-proved-memory-contracts]]** and **[[wp-view-separating-product]]**
  own footprints for `Proved` items and views. The per-slot footprint
  should be the same notion.
- **[[io-image-process-stack]]** owns the process stack that activation
  frames live on.

## Log

- 2026-10-31: docs/native-procedures-design.md §5 takes the derived-contract part: a procedure's claim is Stmt::emit_runs at the callee's Target (its frames on the caller's, one less depth), proved for every procedure at once by induction on the call depth (the linking theorem, depth for Löb). No per-slot footprint is needed for it: the callee's words are its own by the meaning (restored), buffers shared. The footprint, the relational frame for Proved contracts and the two controls stay here.
- 2026-11-01: The meaning now makes the callee's words its own outright (it starts from zero, only its results and buffers come back) and the caller saves its live words, so the derived contract still needs no footprint.
- 2026-11-05: gardener: cites a file it shares with [[native-register-moves-and-convention]] (`docs/native-procedures-design.md`).
