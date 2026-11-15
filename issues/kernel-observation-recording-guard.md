---
title: Guard withheld recordings like unseal recordings, before early cutoff reads them
status: closed
labels: [kernel,state-machine,caching]
area: kernel
created: 2026-11-08
updated: 2026-11-09
---

Give `withheld::record` the drop guard `unseal::Recording` has, ideally as one recording type for both, before early cutoff starts reading it.

## Problem

`crates/kernel/src/unseal.rs` and `withheld.rs` are two thread-local stacks recording which sealed proofs, or which withheld definitions, a judgment opened, so a cache can key on them. `unseal` closes its frame on drop (`Recording`, ~37), and `close` pops any frames left open inside it. `withheld::record` (~29) is a bare push, call and pop. A panic caught further out leaves its frame on the stack, and the outer recording then pops the inner frame as its own and loses what it saw. The elaborator catches panics in the kernel pool's workers (`crates/elab/src/pool.rs` ~119), which wrap only `unseal::record`.

There is no defect today because `withheld::record` has no caller. Its first reader is [[interface-body-early-cutoff]]. After that, a lost frame means a client replayed over a withheld body it did observe.

Review: `docs/kernel/kernel-implicit-state-review.md` §6.

## Proposal

One `Observation { unsealed, glued }` frame with `unseal`'s guard and nesting (or `withheld` reusing `Recording`/`close`), and the pool worker records both. Small, and observational: nothing in the kernel reads a recording.

## Related

[[interface-body-early-cutoff]], [[theorem-witness-unfolding]], [[fmt-budget-state-nesting]] (the other thread-local state that a guard should restore whole).

## Log
- 2026-11-09: done before its first reader. `crates/kernel/src/recording.rs` holds the guard and close protocol once; `unseal` and `withheld` each keep their own frame stack over it. `withheld::record` now survives a caught panic in its span (unit test). Two stacks rather than one `Observation` frame: the callers ask different questions.
