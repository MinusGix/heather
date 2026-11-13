---
title: rt: prove that a pure term's lowered region stores nothing and calls only pure functions
status: open
labels: [native,runtime,proof]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-11
updated: 2026-11-11
---

`FTm::lower` (lib/native/runtime/rt_file_lower.hthr) lowers a pure term
beside functions that write with `Tm::lower`, then checks two facts of the
region by evaluation (`FTm::value_checked`): that it stores nothing
(`StructuredRegion::quiet`) and that every call it makes is of a pure
function (`StructuredRegion::calls_among(FTm::pure(base))`). The bridge
from the term's evaluation to its run reads both
(`StructuredRegion::run_quiet_among`, `FTm::value_sound`).

Both hold of every region `Tm::lower` builds: no case emits a
`BufferStore`, and a `Call` region is emitted only at an index whose
signature is of words (`Tm::lower_call`), which an index past the
signatures is not. So the check never fails on a program whose pure
functions are the ones below `base`, and it costs a walk of each pure
region at every lowering.

## Wanted

Two theorems over `Tm::lower`, by the walk `Tm::lower_static` already
takes:

- `Tm::lower_quiet`: `Tm::lower(t, w, g, ports, next) = Some(c)` gives
  `c.region.quiet().IsTrue()`;
- `Tm::lower_calls`: the same hypothesis gives
  `c.region.calls_among(λ f => Succ(f).leb(w.sigs.len())).IsTrue()`
  (from `Sig::at` past the list being `Sig([], Bit)`, which is not of
  words).

Then `FTm::lower_value` is `Tm::lower` and `base` is asked to be at least
`w.sigs.len()` once, in `FTm::CallsAgree`.

## Why not now

The primitive table (`Tm::lower_prim`) is the long part of the walk, and
the check is cheap beside the certificate. Do it when the generator's
cost per function is measured, or when the loop lowering (4c-2) wants the
same two facts of a loop's pure regions.
