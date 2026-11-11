---
title: Stack loads and stores at a 32-bit displacement
status: open
labels: [native,x86,machine-model]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-11-11
updated: 2026-11-11
---

The stack model's word forms take a byte displacement
(`StackStore`, `StackLoad` in `lib/std/arch/x86_64/x86_64_stack.hthr`:
`mov [rsp + disp8]`), which reaches sixteen slots. That is enough for the
function compiler's frame and too short for a frame that holds a
statement's file of words
(`docs/native-procedures-are-functions-design.md` §2.2), so U5 reaches a
slot through RBX: `MovRI(Rbx, 8 * id)`, `AddRR(Rbx, Rsp)`, then the word
`Load` or `Store` (`Prog::word_to`, `Prog::word_store`, step 5b). One
instruction would do.

## Scope

- `mov [rsp + disp32], r64` and `mov r64, [rsp + disp32]` as stack forms
  (ModRM mod 10, the SIB byte as now), with their bytes, their normal
  path (`StackForm::Executes`), the defined-state lemma, and the `Asm`
  items and run rules the byte forms have.
- The program compiler's slot access as one such form, RBX no longer
  written by it.

## What it assumes from elsewhere

- **[[native-one-compiler]]** owns the frame (U5 step 5b). Assumed here:
  only that a slot is the stack word at RSP plus eight times its id.
- **[[function-ir-verified-live-spills]]** and a future spill slot in the
  function compiler's placement would use the same form.

## Done when

A statement's slot read and write are one instruction each, the tools
pass their GNU gates on it, and a probe reads and writes a slot past the
byte displacement's reach.

## Log

- 2026-11-11: U5's step 5b built the frame, so this now has a measured payoff: every slot read and write is three instructions (two to form the address in RBX), and because RBX is written twice the proofs name the register file after an access instead of computing it ([[native-gprs-writes-not-canonical]]). With a `[rsp + disp32]` form a slot access writes no scratch register, `Target::rbx_gprs` and its lemmas go, and the start-up's zeroing and the argument moves shrink by two items a word.
