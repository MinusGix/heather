---
title: The fast lane grew 6x with the wc command's library tests; where the suite's time goes (2026-10)
status: open
labels: [testing,performance,tooling]
area: infrastructure
created: 2026-10-11
updated: 2026-10-21
---

A fresh look at what the suite spends, after the wc command rounds
(C1–C4, the label assembler, the Runs triples) landed on top of the
2026-09-24 state that [[fast-lane-heaviest-declarations]] and
[[rust-edit-loop-build-bound]] left. Measured on a 4-CPU cloud container
(slower than the desktop; read the shapes and ratios, not the seconds).

## What was found

The fast lane's test phase, warm, was **890 s wall for 881 s summed /
1048 CPU-s** (the 2026-09-24 desktop snapshot: 151 s summed / 185 CPU-s).
Three causes, ranked by what they cost the loop:

1. **The wc library tests re-elaborated the command's library from source in
   every test** — [[suite-tests-reelaborate-library-modules]]'s pattern,
   back in the new files. `stat_width_process`, `row_fields_process`,
   `arg_scan_process`, `format_width_process`, `read_filter_process`,
   `field_line_*`, `open_read_close_process`, `read_loop_process`,
   `linux_determinism` and the read-loop fixture's `checker()` itself each
   built the x86 prefix by image and then elaborated 17–27 library modules
   (`linux_x86_64_io`, `x86_64_asm`, `elf64_runs`, `elf64_format_width`,
   `elf64_stat_width`, …) with `elab_module_source`. Per-test declaration rows
   (`HEATHER_TIMINGS_DIR`): `stat_width_library_checks` was 124.6 s, of which
   the test's own client was 0.34 s and `elf64_stat_width` alone 59 s
   (92 % gate). Summed over the fast lane's tests, ~545 s of the 881 s was
   library modules re-elaborated from source; the full lane's
   `slow_acceptance_*` refusal tests paid the same base again before their
   mutants.
2. **The runner ran one target at a time on a 4-CPU box.** The automatic CPU
   bound was `floor(cores / 2) − 1`: two CPUs per child minus a slot kept
   free for the editor, which on 4 CPUs is half the box.
3. **The doc pass compiled a second O3 elaborator after every elab edit.**
   `cargo test --workspace --doc` builds `heather-elab-unit`'s rlib although
   its `[lib]` says `doctest = false` (`--doc` does not honour it), and the
   workspace has no doc tests at all. After a one-line elab body edit: 41 s of
   the doc pass, serial, at the end of every suite (the `--no-run` build
   before it is 71 s on this box).

## What changed

- `support/read_loop.rs`: `checker_with(extra)` replays the x86 prefix, the
  read-loop list and `extra` through `support::semantic_test_base`, and
  `checker()` is `checker_with(&[])`. Every converted test keeps its exact
  module list and order; the module a `*_library_checks` test is about goes
  in the replayed list (checked from source by whichever test first asks for
  that list, and by the full lane's exact policy whenever the compiler
  changes), and the test's client, generated pieces and mutants go through
  the real kernel as before. A `slow_acceptance_*` test's unmutated base is
  replayed; its mutants are not.
- `scripts/run-test-targets.mjs`: the editor slot is kept only on boxes of
  eight or more CPUs (4 CPUs → 2 jobs; 16 → 7, unchanged); the doc pass
  excludes `heather-elab-unit`.

Fast lane, warm, same box: **890 s → 210 s wall** (summed 881 → 400 s,
CPU 1048 → 529 s), 3051 passed. The converted targets, warm, alone:
`stat_width_process` 122 → 1.3 s, `row_fields_process` 61 → 1.2 s; the
others now cost what their own pieces and mutants cost.

Full lane after the change, same box: **3229 passed in 13.5 min** (compile
69 s + warm-ups + tests 549 s; summed 1061 s, CPU 1323 s). The
`slow_acceptance_*` refusal tests now pay only their mutants:
`stat_width_refusals` 68.8 CPU-s (it was at the 300 s rail,
[[stat-width-refusals-test-cpu-rail]]). Its heaviest targets:
`native_wc` 166 CPU-s (the only one past half the rail),
`command_refusals` 100 s, `stat_width_refusals` 69 s, then the field pieces
and the other refusal tests at 25–45 s.

## What is left, ranked (fast lane, warm, after the change)

The lane is now throughput-bound (summed 400 s over two jobs ≈ its 204 s of
tests), so further cuts are per-test work. Every one of these is generated
certificate content, i.e. the native line's own cost, not harness overhead:

| test | s | what it is |
|---|---|---|
| `field_line_high_format::field_high_certifies` | 49 | generated `field_high` piece, ~44 s in its own module, plus a refused mutant |
| `field_line_format::field_low_certifies` | 37 | the same for `field_low` (~33 s own) |
| `function_ir_loop_trace::record_state_loop_certificate_checks` | 27 | `wc_pieces` 12 s, `wc` 7.5 s |
| `function_ir_narrow_certificates::narrow_fused_branches_check_and_refuse_another_test` | 26 | four branch mutants at ~6 s each |
| `filter_step_generation` (16 tests) | 50 wall / 93 CPU | `squeeze_pieces` ~12 s in each of two tests, `wc_pieces` 10 s |

The field pieces are the cheapest lead: one generated function's
certificate costing ~40 s of kernel time is the kind of shape
[[structured-certificate-cost]] and [[fast-lane-heaviest-declarations]]
found and fixed before (a spelling that misses the shortcut, or a layout
restated per node). Probe with `--only` per [[check-single-item-measurement]].

Outside the test phase:

- **Rust-edit build**: 71 s on this box after an elab body edit; the floor
  [[elab-rebuild-floor]] closed with no lever left.
- **Cold warm-ups**: the command prefix is 157 + 67 s on a cold store
  (`semantic_command_warmup`), the largest cold cost in the fast lane; it is
  paid once per lib change, then replayed in ~2 s.

## Second pass: the heavy tests (2026-10-12)

- **`field_high` / `field_low`**: a declared type was lowered again at every
  mention ([[named-type-lowering-per-mention]], now memoized). That cut the
  declarations that only name `StructuredCode` about fourfold but
  `field_high`'s own module only 65.7 → 60.1 s of item time: the rest is
  spread over the per-node declaration kinds. Item seconds summed by kind
  (`field_high`, debug build, width one):

  | kind | n | total | gate | body | note |
  |---|---|---|---|---|---|
  | `decodes` | 247 | 7.5 | 0.6 | 1.5 | elab `whnf` 3.0, `instance_match` 1.9 |
  | `correct` | 247 | 6.5 | 4.6 | 1.1 | |
  | `graph` | 124 | 6.0 | 3.8 | 0.3 | |
  | `byte_length` | 247 | 4.1 | 0.3 | 3.5 | |
  | `preserves` | 247 | 3.9 | 1.7 | 1.4 | |
  | `layout` | 247 | 3.5 | 0.5 | 0.9 | |
  | `leaf_value_*_after_node_*` | 152 | 3.4 | 0.6 | 1.6 | |
  | `leaf_instructions` | 124 | 3.3 | 1.0 | 0.2 | |
  | `bytes_are` | 247 | 3.2 | 1.1 | 1.9 | |

  One `decodes` (`--only`): 12.7 ms, of which `whnf` 7.5 ms over only ~300
  evaluation steps and two `instance_match` calls 2 ms — work proportional to
  the size of the lowered `StructuredCode`/`Instruction` types rather than to
  the proof, [[elab-whnf-copies-straight-continuations]]'s shape. That is the next lead
  for these two tests; nothing in them is harness overhead.
- **`record_state_loop_certificate_checks`** elaborated `omega`,
  `bitvec_omega` and its own fixtures `wc` (whose growth proof runs `omega`)
  and `wc_context` from source; they are the loop generator's inputs and now
  replay with the base (`wc_checker`), leaving `wc_pieces` and `wc_native`.
- **`narrow_fused_branches_check_and_refuse_another_test`** checked four
  certificates and fourteen mutants serially; now one test per case, so they
  run on the process's test threads.
- **`filter_step_generation`**: each step's certifying test and its refusal
  elaborated the same generated pieces (`squeeze_pieces` twice, likewise
  `drop`, `eq_drop`, `if_drop`); `with_pieces` builds each once per process.

## Log

- 2026-10-12: Second pass over the heavy tests: named-type lowering memoized (named-type-lowering-per-mention), loop_trace fixtures replayed, narrow_fused split per case, filter-step pieces shared per process. field_high's remaining cost attributed by declaration kind.

Measured A/B (the `function_ir` family binary before and after this pass,
same replayed images, two test threads, width one, same box, 2026-10-12):

| target | before | after |
|---|---|---|
| `field_high_certifies` alone, wall | 75.0 / 78.6 s | 75.4 / 73.1 s |
| `record_state_loop_certificate_checks`, CPU | 40.0 s | 22.1 s |
| `filter_step_generation`, CPU (wall) | 132 s (69 s) | 109 s (69 s) |
| `function_ir_narrow_certificates`, wall | 47 s | 28 s |

The memo does not move `field_high` end to end. Its warm fast-lane time was
49 s in the first pass and is ~75 s on this box today at every commit back to
the first pass's own (542609c: 78.5 / 81.2 s alone), so that is the box, not
#27 or #28. `filter_step_generation`'s wall is held by its counting tests
(`wc_counting_piece_certifies`, `decided_connective_counting_piece_certifies`,
`record_update_counting_piece_certifies`, 15–18 s each), which elaborate
different steps and share nothing.
- 2026-10-13: field_high's generated certificate reshaped ([[field-high-certificate-shape]]): standalone check 39.9 → 15.8 s, field_low 28.6 → 11.1 s.
- 2026-10-21: B1 ([[native-burn-process-stack]]) deleted the wc command's library, its elab process tests, the command warm-ups and the native_wc/native_tr/native_filter/native_read_loop gates, so the growth this issue attributes to them is gone; what remains is re-read from the next suite's timing table.
