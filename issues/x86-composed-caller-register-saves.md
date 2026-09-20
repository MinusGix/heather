---
title: Save live and ABI registers for composed callers with larger leaves
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Problem

The first reusable composed-function summary reserves RCX/RDX for original
inputs and R8–R11 for live temporary values. Its arithmetic leaf therefore has
only RAX available as a scratch destination. This makes ABI preservation
simple and explicit, but rejects leaves that need additional temporaries.

## Acceptance

- Support a composed caller whose leaf needs more than one scratch register.
- Derive saved/live values from the caller plan and the leaf's actual clobber
  contract. Save and restore any ABI-preserved registers the composed function
  itself uses, or introduce checked caller slots for live values.
- Preserve source, fetched-execution, return-target, stack-restoration, and
  memory-footprint claims. Protect parent return and live slots from children.
- Exercise a live value across a multi-register leaf and reject corrupted save,
  restore, overlap, and clobber evidence.

## What it assumes from elsewhere

- [[x86-composed-caller-summary]] owns the initial callable summary profile.
- [[x86-call-memory-footprints]] owns generic frame allocation/aliasing.
- [[x86-caller-value-sharing]] owns recovery of shared source values, not frame
  policy or register-save conventions.

## Log

- 2026-09-19: The RAX-only restriction is removed for cases that fit without a save frame. Leaf selection now uses a scratch pool ordered RAX/R11/R10/R9/R8/RCX/RDX. Caller allocation derives the actual destination set, retains two inputs plus shared values in untouched scratch registers, and discards clobbered facts at each call. Preservation claims remain kernel-checked against the actual instruction stream.

  The multi_register fixture requires RAX and R11 while a caller value stays live across both calls; its neutral-state source/ABI/return/memory summary passes. An unreported child clobber is refused locally. Exhausted disjoint pools still produce an explicit unsupported-spilling error.

  Still open: checked stack saves/reloads and ABI save/restore frames for cases that do not fit the disjoint pool, including saved-slot overlap and corrupted restoration controls. The current work does not allocate saved slots or claim that acceptance item is complete.
- 2026-09-19: Final plain scripts/test passed: 2830 passed, 0 failed, 5 ignored. The multi-register ELF executed with status 108, and the neutral-state summary and clobber-refusal tests passed. The disjoint-register allocation is verified; checked stack saves/restores remain open as described above.
- 2026-09-19: Implemented a bounded checked-save profile. The selector first tries untouched scratch registers, then retries with one borrowed leaf destination. Its DAG use counts decide whether that register's current value crosses a call; only those calls receive a save and restore. The existing alignment word at 0x401ff0 is the save slot, disjoint from the child return word at 0x401fe8 and parent return word at 0x401ff8. No ABI-preserved register is allocated.

  Generic proofs reconstruct arbitrary saved words from checked byte stores over neutral memory, carry the saved-word equality through the child CALL and leaf memory contract, and establish the actual load's register value. The composed footprint is the union of child return writes and the save word when present. Restoring registers/RSP does not claim to restore dead memory bytes. Concrete execution still checks canonical bytes, fetches, permissions, alignment, and every successor.

  Focused tests accept the neutral-state summary and refuse wrong saves, restores, slot overlap, and unreported child clobbers. The native one-call ordinary/wrapping cases passed; the final fixture now reuses the slot around two calls and is in the running full suite. Named canonical instruction equalities keep operand mutations local before whole-memory conversion.

  Residue has explicit owners: [[x86-composed-caller-multi-slot-spills]] owns multiple simultaneous saved words and ABI save frames. [[x86-leaf-summary-neutral-scaling]] records a larger arithmetic leaf's existing OutOfFuel failure before any caller save proof. No resource limit, kernel rule, or proof-library definition changed.
- 2026-09-19: The first full run exposed a second-call OutOfFuel in scratch-register preservation after a save/restore. Replaced the call-site reflexive preservation claim with a small generic theorem over an arbitrary leaf-entry state for each untouched scratch register. The two-call neutral-state/refusal test and both native inputs now pass under unchanged budgets.

  The final regression fixture additionally changes the saved value between calls, so slot reuse must overwrite and recover two different values. Final full-suite verification is running on that fixture.
- 2026-09-19: Final plain scripts/test passed: 2831 passed, 0 failed, 5 ignored. The final native fixture changes the saved value between two calls and reuses the same checked slot; ordinary and wrapping inputs execute with statuses 88 and 4. Neutral-word/memory proofs and wrong-save, wrong-restore, overlap, and clobber refusals pass. Existing native and scaling gates also pass under unchanged budgets.

  The bounded one-slot save/restore milestone is complete. Multiple simultaneous slots and ABI save frames retain [[x86-composed-caller-multi-slot-spills]] as their owner; the independently observed larger-leaf summary limit remains with [[x86-leaf-summary-neutral-scaling]].
- 2026-09-19: The one-slot profile has been extended to multiple simultaneous scratch-register saves in [[x86-composed-caller-multi-slot-spills]]. That extension leaves ABI-preserved registers untouched; future ABI-register allocation and incoming-value saves remain with [[x86-calls-stack-frames]].
