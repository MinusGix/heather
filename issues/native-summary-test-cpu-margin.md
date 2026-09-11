---
title: The two-placement native summary test runs within 25% of the CPU rail and tips over under suite load
status: open
labels: [x86,testing,performance]
created: 2026-09-09
updated: 2026-09-11
---



`two_placed_calls_share_one_summary` (`crates/cli/tests/native_summary.rs`)
spawns `heather build-x86` under `scripts/test`'s `ulimit -t 300`. Measured
alone on a warm furnace box (2026-09-09, one release build, cap lifted to
900 s): **226 s CPU** with [[bitvec-width-bounded-defaults]] applied, **233 s**
without — so the test has no headroom to speak of, and in a plain full
`scripts/test` on the same box it was SIGKILLed at 300 s once while the same
tree's previous full run passed. The parallel suite (several 4 GiB children on
8 OCPUs) inflates CPU time enough to cross the rail; the test's own cost did
not move.

[[x86-native-certificate-cpu-budget]] brought it from over the rail to 224 s
and closed; this is the residue: a gate that passes or fails on host load is
not a gate. Options, in preference order: attribute and shrink the
certificate's cost (that issue's log names byte-fetch declarations as the bulk,
[[generated-proof-cost-diagnostics]] owns the tooling); split the check across
two children so each is well under the rail; or run it serially the way
[[mutual-recursion-test-rail]] keeps its target inside the rail. Do not raise
the rail or shrink the example.

## What it assumes from elsewhere

- **[[x86-native-certificate-cpu-budget]]** owns the 224 s datum and the
  prefix-skip helper; assumed here only that nothing since changed the cost
  (the A/B above says the swap did not).
- **[[mutual-recursion-test-rail]]** owns the serial-rail mechanism if that is
  the route taken.

## Log

- 2026-09-09: Route 2 taken (2026-09-09): native_summary is now an exclusive target in scripts/run-test-targets.mjs (the frontend_bench_smoke mechanism: sorted last, runs alone after the parallel phase), so its 226-233 s alone is what it pays, not the contended 294 s. Costs ~4 min of full-suite wall on an otherwise idle box; the certificate-cost route (option 1) stays open as the real lever. Same round: the fast lane now skips all six native certificate gates and their warmup (~1200 CPU-s that no elaborator edit iterates on).
- 2026-09-09: Verified on furnace (2026-09-09, warm box): full lane 2530 passed, native_summary 225.39 s alone as the exclusive target, suite 572 s wall; the fast lane dropped 461 s -> 195 s wall with the native gates skipped. Two further certificate-bearing unit tests (elf_header_mutations_are_rejected_by_heather, call_stack_semantics_and_refusals; 180 s together) were still in the lane on the first pass and are now skipped too.
- 2026-09-09: Route 1 (shrink the certificate) took a first bite. Measured with the new `--item-timings` flag ([[generated-proof-cost-diagnostics]]) on one warm furnace box, release profile, same box before and after: summed item time for examples/x86-native/reused_callee.hthr **192.1 s -> 164.0 s**, and the dominant family — the per-code-byte fetch declarations — **88.6 s -> 43.6 s**. What changed, all in crates/cli/src/native/calls.rs plus two list lemmas: the certificate's file bytes are no longer `[…]` literals (a dependent-vector fold that is re-run from the front at every lookup and costs seconds just to build: the 232-byte header alone was 4.3 s) but a chain of one-cons suffix definitions; each code offset's suffix is named once in a forward `drop_succ` pass, so a byte lookup is `nth_drop` plus one head read instead of a re-traversal; each byte's fetch premises (page, offset, found, present, no-wrap, next-rip) are named theorems, which both attributes them and, measurably, checks faster than inlining them; and the per-instruction fetch chain is nested in one declaration since stating a `FetchedFrom` is work proportional to the span left. In the suite (dev/test profile, same box): native_summary **225.4 s -> 202.3 s**, native_stack_local 196 -> 168 s, native_calls 152 -> 145 s, whole suite 2530 passed / 0 failed. Still no headroom worth the name: the residue is inside `fetch_span_more`/`ReadableBytes` at ~0.26 s per byte level, which is a lib-shape question this round did not open. The exclusive-target arrangement stays.
- 2026-09-10: Both follow-ups of the 2026-09-09 round taken. (1) The non-callee ELF path (crates/cli/src/native/elf.rs) got the same three changes as the callee path: header and code as named-suffix chains with one forward `drop` pass, per-byte premises as named theorems through `static_elf64_read_split` (moved from elf64_calls to elf64_load under that name, since both profiles read a header-plus-code file) and the new `static_elf64_observation`/`static_elf64_fetch_one`/`static_elf64_fetch_more` wrappers (elf64_load; the premise is spelled as the access's own projection, which is what keeps the kernel from unfolding the file read from the front), and the per-instruction chain nested in one declaration. examples/x86-native/mix.hthr, release with the sampler feature on, same furnace box before and after: certificate item time **55.7 s -> 37.3 s**; the per-byte `read`/`permission` refls (171/158 ms each, a from-the-front `nth` twice per byte) became ~47 ms `read` + ~41 ms `found` + ~47 ms `page`. (2) The residue was attributed, not the shape the round guessed: see [[unnameable-annotation-occurrences]]'s log of this date. In one line: every `call_file_fetch_more` / `static_elf64_fetch_more` application pays ~600 typing-seam conversions for the kernel's re-check of the ten stored application annotations, ~100 of which decode a value-indexed record type spelled inline (7.7 K chars of Wf/Σ code) against the same type spelled by reference at 2-3 ms each. Measured constant per application: five probe shapes (named-suffix vs explicit-list `rest`, nested vs split chain, bit-list vs numeral addresses, 232- vs 4-byte header) all missed ~4070 times for 40 levels. Nothing in lib/std/arch/x86_64/fetch.hthr is implicated; the lever is the elaborator's annotation spelling or a kernel memo, not the lib.
- 2026-09-10: Route 1, second bite (2026-09-10): the fetch-chain residue's larger half was a closed spelling disagreement in the elaborator (`project_field`'s fallback walk; [[unnameable-annotation-occurrences]]'s log of this date), not the open instance. Same furnace box, release with the sampler on, before → after: reused_callee `caller_native_byte` 51.4 s → 36.3 s (kernel 48.5 → 33.5 s), certificate item sum 195.3 s → 184.4 s; mix `mix_native_loaded_byte` 13.5 s → 8.3 s (12.4 → 7.1 s), certificate 38.6 s → 33.0 s. The exclusive-target arrangement stays; the per-level residue now names an implicit type argument's code-literal spelling (inherent until instances are nameable) and the elf path's inline address literals.
- 2026-09-10: Route 1, third bite, by [[per-instantiation-type-codes]] (2026-09-10): build-x86 mix whole run 34.07 → 18.25 s item time on one box (byte family 7.92 → 3.94 s); the fetch residue's implicit-argument half is gone. native_summary itself stays under the exclusive-target arrangement; re-measure its margin before loosening it.
- 2026-09-11: 2026-09-11 re-measure, furnace, dev/test, warm target, one run: native_summary 135.9 s as the exclusive last target (was 202.3 s on 2026-09-09 before 94b7694/bc07438/9ae0855; different instance, so the box variance of ~35% applies). That is 45% of the 300 s rail, i.e. the margin the issue asked for before loosening the exclusive arrangement — but confirm on a second instance before dropping it, since one run cannot separate the three rounds' effect from box variance.
- 2026-09-11: 2026-09-11 note (from the callee-sharing scoping): ulimit -t is RLIMIT_CPU, inherited but counted per process, so each build-x86 child spawned by a test gets its own 300 s and the test binary itself burns almost none. The exclusive slot therefore protects the child from contention, not from a summed-CPU rail; the margin question is about contention slowdown, not aggregate CPU.
