---
title: "push_gen_def's kernel gate is not wrapped in stats::time_kernel"
status: closed
labels: [elaboration, performance, testing]
created: 2026-08-06
updated: 2026-08-16
code: crates/elab/src/gendefs.rs:262 @ 77cb9b4
---

Found by the cache-v1 round (2026-08-06, [[parallel-checking-and-caching]])
while installing the gate oracle at both kernel-gate sites: the
`elab_decl_inner` site times its `check_type`/`check_term` pair with
`stats::time_kernel`, but the `gendefs::push_gen_def` site does not — so
`docs/infrastructure/frontend-benchmarking.md`'s `kernel` phase undercounts by exactly the
generated definitions' gate cost, despite that doc saying the phase covers
"every finished declaration".

The fix is a two-line wrap, but it *changes what the phase split reports*:
inductive-heavy fixtures will show a larger kernel share and a smaller
elaborate share after it. So it wants a deliberate small round that also
re-reads the recorded phase-split observations in
`docs/infrastructure/frontend-benchmarking.md` for any that the correction invalidates
(the 98.8%-kernel-gate headline for ir_v1 was measured through the CLI's
wall clock, not this counter, so it should stand — verify rather than
assume). The exponent gates compare total time and are unaffected.

## When

Triggered: the next time frontend phase-split numbers are used to argue
anything, or alongside the next frontend-bench round — whichever comes
first.

## Log

- 2026-08-16: LANDED. push_gen_def's kernel gate is wrapped in stats::time_kernel, so the frontend suite's 'kernel' phase now covers every finished declaration, which is what docs/infrastructure/frontend-benchmarking.md always said it covered. All three gate sites are timed (gate.rs is the authority on the list: elab_decl_inner, push_gen_def, quote.rs's elab_meta_decl_inner — the last one gained its wrap with the elaborator-snapshot round), and resolve.rs's trial checks were already wrapped.

THE ISSUE'S OWN PREMISE WAS WRONG, and it is worth recording because it is what the round was told to verify rather than assume. The 98.8%-kernel-gate headline for ir_v1 was NOT 'measured through the CLI's wall clock': the phase split IS this counter — benches/frontend/fixtures/mod.rs reads stats::kernel_ns() into Phases — so the correction moves that headline directly. It stands anyway, and for a stronger reason than the one guessed: the shift is a fraction of a point, and it is UPWARD.

Measured rather than reasoned, paired before/after on one machine (minus-desktop, release, corpus/check-file, back to back with nothing else running) — kernel share, before -> after: vec_code.hthr 14.6% -> 15.5%; ir_v1.hthr:decls 79.1% -> 80.8%; ir_v1.hthr 90.5% -> 90.6%. Direction is the predicted one (kernel up, elab down) at every case, magnitude <= 1.7 points, which is inside the doc's own noise warning for a split read from one instrumented run. NO recorded observation is invalidated; the issue's worry that 'inductive-heavy fixtures will show a larger kernel share' is true and too small to matter.

SEPARATE FINDING, nothing to do with this fix (both builds show it): docs/infrastructure/frontend-benchmarking.md's 'day one' phase-split numbers have aged badly. Recorded: ir_v1 parse 0.0% / elab 1.2% / kernel 98.8%, corpus/check-file at 67 s. Measured today: 0.1% / 9.3% / 90.6% at 2.71 s. The elaborator did not get slower — the kernel-side rounds that landed in between moved the absolute by better than an order of magnitude, so the elaborator's SHARE grew. The section is now marked as day-one and dated, with the reading that survives (a proportion is not a measurement; the leverage claim is the point) and a pointer here for current figures, per the numbers-in-docs policy on [[perf-tracking-consistent-environment]]. The phase table's 'kernel' row now points at gate.rs for the site list rather than restating it.

Suite 1649, unchanged — a timing wrap adds no tests. Worth noting what the existing ones now do: crates/cache/tests/end_to_end.rs asserts kernel_ns() == 0 on a fully warm run in two places, and those assertions are STRONGER after this change, since before it a generated definition's gate could have run warm without moving the counter at all. They pass, so gendefs really are admitted warm.
