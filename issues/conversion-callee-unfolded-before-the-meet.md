---
title: A callee's body is compared when one side of a conversion reaches its call first
status: open
labels: [native,runtime-fn,performance,kernel]
area: heather-in-heather
created: 2026-11-12
updated: 2026-11-12
---

Found scaling a `runtime fn` of a laid record ([[sha256-context-type]]). Two costs of one cause: the kernel reached a callee's call on one side of a comparison before the other side had computed down to it, unfolded the callee, and compared bodies.

**A reader built from two calls of another reader.** `List::u64_be_within` is `u32r(i) << 32 | u32r(i + 4)`. In a pin by conversion (a reflection's meaning against the function written out) with the program's own accessors, a store costs a few thousand steps and a 32-bit read almost nothing, and each distinct 64-bit read about a quarter of a declaration's budget. Stand-in readers showed the shape: one call of another reader in the body is cheap, two under a strict operator are not, and a helper around the operator does not help. A function of four 64-bit fields could not be pinned.

**The meeting window.** `Conv::tm_w` remembers the spines a side was advanced past so the other side can meet it there (`Passed`), eight of them. A written function passes one defined head per value it binds and per store, so past about eight statements the name both sides share has been evicted, the meet fails, and both sides are compared unfolded, which is the first cost again at every read.

What this round did, in the library: the generator of a function of a laid record writes the function as a function of its callees and proves each statement that is by conversion (the instance's pin, the bytes' meaning, the program's answer) at every callee, then reads it at the program's own (`HWorld::at`, rt_held.hthr). A parameter has no body to unfold. Cost is then linear in the function, and seventeen statements over seventeen fields pass.

What is left:

- `runtime_span` and `runtime_reads` (a function over a span written by hand, a function that only reads) still prove their pin at the program's own callees. The same change applies to them and has not been made: they pin the written function itself, which meets its reflection's meaning differently, and none has yet failed for this reason. SHA-256's block functions call no 64-bit reader.
- A client restating a published `runs_over` through a projection (`program_run(…).word = f::bytes(…).value`) has the kernel enter the function's body, and it runs out. Stated as published it is immediate. The published form is the one to cite, and a `word`/`span` pair of read-outs could be published beside it.
- For the kernel: whether eight is the right window, and whether a failed meet could be retried by name before both sides are unfolded. Recorded, not asked for.

Related: [[conversion-proof-compared-at-computed-type]], [[runtime-link-compares-functions]], [[runtime-measured-reader-heavy-callee]], [[conversion-fuel-failure-says-where]].
