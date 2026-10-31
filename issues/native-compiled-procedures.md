---
title: Compile calls to procedures with frames, derived contracts and a register convention
status: open
labels: [native,x86,compiler]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-10-31
updated: 2026-10-31
---

Round R8 of `docs/compiler-milestones-proposal.md` (§4.2 N2, §7), milestone `nh-procedures`: calls that are
not inlined.

## Scope

- A compiled call to a procedure, with its frame on the process stack ([[io-image-process-stack]]), its contract derived from its body ([[native-procedure-contracts]]), and a register convention ([[native-register-moves-and-convention]]).
- Recursion that is not a tail loop.
- `grep -F`, with a shared line-buffer helper, as the customer (it moved here from `hih-tools`).

## Done when

A helper called from several sites is emitted once, a non-tail recursive function compiles, and `grep -F` passes GNU tests under `LC_ALL=C`.
