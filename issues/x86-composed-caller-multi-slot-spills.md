---
title: Allocate multiple checked save slots for composed callers
status: closed
labels: [compiler,x86,proofs]
created: 2026-09-19
updated: 2026-09-19
---

## Scope

Extend the bounded composed caller beyond one simultaneously saved word.
The first checked-save profile borrows at most one leaf-clobbered register and
uses the existing eight-byte alignment slot, with actual liveness deciding
which calls need a save. That initial profile refused cases needing more saved words; this extension
allocates them within the existing six-register bound.

## Acceptance

- Allocate multiple caller-owned slots from live values and actual child
  clobbers, with a checked frame extent and preserved call alignment.
- Prove save/reload value identity and non-overlap with other live slots,
  child return words, and the parent's return word.
- If ABI-preserved registers are allocated, save and restore their arbitrary
  incoming values and retain the composed ABI contract.
- Exercise multiple simultaneously live saved values and reject stale saves,
  reloads, slot overlap, missing restoration, and footprint evidence.
- Keep source, fetched-execution, stack-access, return-target, and memory-effect
  claims within normal checking; do not silently expand resource limits.

## What it assumes from elsewhere

- [[x86-composed-caller-register-saves]] owns the completed one-slot profile.
- [[x86-call-memory-footprints]] owns general frame extent/aliasing interfaces.
- [[x86-caller-value-sharing]] supplies last-use information for shared values.

## Log

- 2026-09-19: Implemented liveness-based borrowing of multiple leaf-clobbered scratch registers, distinct live save slots, and an odd-word frame extent preserving call alignment. Generic saved-word facts survive writes to every other live slot and child return word; the composed footprint contains exactly the written words, excluding padding. ABI-preserved registers remain untouched. A two-slot fixture passes neutral-state checking and ordinary/wrapping native execution (66/253); targeted controls reject stale saves/reloads, missing restoration, aliased live slots, and omitted footprint evidence. Full plain `scripts/test` is running under unchanged limits.
- 2026-09-19: The first full run completed every other target but killed the CLI unit-test binary at its unchanged 300-second CPU rail (2817 passed before death, 0 assertion failures). Refactored the caller mutation harness to check each common leaf prefix once, then fork that checked environment; the omitted-footprint control likewise reuses the already checked state/memory facts before independently checking its changed postcondition. Every acceptance and refusal remains enabled. A fresh plain full-suite run is underway.
- 2026-09-19: Final plain `scripts/test` passed 2832 tests, 0 failed, 5 ignored in 277 seconds wall time. The generic acceptance and all save/restore/overlap/footprint controls pass; both native input cases pass. CLI unit checks finish at 277.0 CPU-s under the existing 300-second rail; [[x86-composed-summary-test-cpu-margin]] tracks further headroom. No kernel, proof-library, or resource-limit changes. Closing the multiple simultaneous scratch-register save-slot milestone; general expression spilling and ABI-register allocation remain with [[x86-calls-stack-frames]].
