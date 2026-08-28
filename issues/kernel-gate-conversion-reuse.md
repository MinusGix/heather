---
title: Reuse repeated successful conversions within one kernel gate
status: closed
labels: [kernel,conversion,performance]
created: 2026-08-28
updated: 2026-08-28
---

Large dependent declarations can ask the checker to establish the exact same
conversion judgment many times.  Each request formerly built a fresh value
arena and repeated normalization even though the ambient world and local
scope had not changed.

## Acceptance

- Reuse only a previously successful, exact conversion judgment inside one
  public kernel gate.
- Include every semantic input in the authoritative equality check; pointer
  identities may partition candidates but must not decide convertibility.
- Do not cache failures or weaken the zero-fuel boundary.
- Bound both adversarial collision cost and total retained memory.
- Preserve the differential, fuel-threshold, and kernel benchmark suites.
- Demonstrate a same-session improvement on the motivating x86 declaration
  without regressing a mostly-distinct frontend workload.

## Log

- 2026-08-28: LANDED.  Profiling a single real `ByteDecode` arm found 1,042
  variable `El`/`Sum` conversions but only 98 exact judgments, with one
  repeated 48 times.  The typing seam now short-circuits syntactic
  reflexivity and retains successful cross-head conversions for the lifetime
  of one `Tc`.  Hits require exact Ψ/Γ/layer/universe/level/type agreement;
  shallow owning `Rc` identity keys are only hash-bucket hints.  They observe
  an address only while hashing a live `Rc`, so cached bare pointers and their
  allocator-reuse invariant are avoided.  Buckets are capped at four entries
  and the gate at 4096.

  Two broader prototypes were rejected.  Memoizing same-head judgments, then
  merely adding scope identity to their coarse buckets, made deep nested
  inference appear 11.7x and 3.9x slower against the stored benchmark because
  candidates were scanned linearly.  Hard bucket bounds and a clean
  same-session baseline showed the saved timing was also stale; nevertheless
  cross-head-only reuse is the smallest policy directly supported by the x86
  profile.

  Against untouched `e4c7c7c` in the same session, the final owning-key
  version moved the x86 module from 30.590 s total / 23.004 s kernel to
  28.372 s / 21.050 s.  With memo lookup disabled but the reflexivity seam
  retained it took 30.182 s / 22.569 s.  A first owning-key draft constructed
  several `Rc` tokens even for excluded same-head judgments and lost the win
  at 30.306 s / 22.532 s; moving key construction behind the cross-head test
  recovered it.
  The frontend depth-32 nested-inference kernel took 41.96 ms untouched and
  27.77 ms with lookup disabled, confirming that the saved 8.38 ms comparison
  was not a usable A/B baseline.
