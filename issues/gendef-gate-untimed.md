---
title: "push_gen_def's kernel gate is not wrapped in stats::time_kernel"
status: open
labels: [elaboration, performance, testing]
created: 2026-08-06
updated: 2026-08-06
code: crates/elab/src/gendefs.rs:262 @ 77cb9b4
---

Found by the cache-v1 round (2026-08-06, [[parallel-checking-and-caching]])
while installing the gate oracle at both kernel-gate sites: the
`elab_decl_inner` site times its `check_type`/`check_term` pair with
`stats::time_kernel`, but the `gendefs::push_gen_def` site does not — so
`docs/frontend-benchmarking.md`'s `kernel` phase undercounts by exactly the
generated definitions' gate cost, despite that doc saying the phase covers
"every finished declaration".

The fix is a two-line wrap, but it *changes what the phase split reports*:
inductive-heavy fixtures will show a larger kernel share and a smaller
elaborate share after it. So it wants a deliberate small round that also
re-reads the recorded phase-split observations in
`docs/frontend-benchmarking.md` for any that the correction invalidates
(the 98.8%-kernel-gate headline for ir_v1 was measured through the CLI's
wall clock, not this counter, so it should stand — verify rather than
assume). The exponent gates compare total time and are unaffected.

## When

Triggered: the next time frontend phase-split numbers are used to argue
anything, or alongside the next frontend-bench round — whichever comes
first.
