---
title: Memory-bound certificates: an allocation-metered platform model
status: open
labels: [design,runtime,compiler,metatheory]
area: heather-in-heather
milestone: [hih-memory]
created: 2026-08-14
updated: 2026-08-14
---

Filed from the datarepr design discussion (2026-08-14, [[datarepr-separation]]):
the space analog of the IR's depth-fuel semantics. If the platform model
meters allocation (each alloc spends against a budget, failure is the
model's reported outcome), then "peak allocation of this program ≤ f(input)"
becomes a provable theorem — which is what makes a claim like "cannot blow a
4 GB limit" *sayable* without trusting the OS's overcommit-lying allocator.
Complements, does not replace, the trusted-boundary stance recorded on
datarepr: actual exhaustion (OOM-killer, overcommit) stays outside the
semantics like the power cable; the metered model bounds what the program
*requests*. Unscheduled; no customer yet. Natural trigger: the first
platform-model round (datarepr v2+), or a user program wanting a stated
memory envelope.

## Log

- 2026-08-14: Referenced substantively by docs/datarepr-design.md (§2.3, §5.2): the OutOfMem strengthening ladder erases arms only relative to an assumed capacity, and this issue's metered model is named as the refinement of that stance when a customer wants a stated envelope.
