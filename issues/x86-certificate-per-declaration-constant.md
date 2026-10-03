---
title: The x86 call certificate costs a per-declaration constant, half of it the frontend re-elaborating generated source
status: open
labels: [x86,performance,elaboration,compiler]
created: 2026-09-23
updated: 2026-10-03
---

The generated x86 call certificate costs a **per-declaration constant**, not a
few heavy proofs, and half of that constant is the elaborator.

Evidence (perf snapshot `perf/snapshots/2026-09-23T140408Z-local.json`, the
corpus entry `examples/x86-native/reused_callee.hthr` through `build-x86
caller --callee leaf`, release, cold, kernel width one; raw table
`target/perf/2026-09-23T140408Z/reused_callee-cold.tsv`, explorable in
`scripts/perf serve`):

- `caller_native_certificate` is 3,477 generated declarations, 12.3 s: p50
  1.9 ms, p90 6.6 ms, max 188 ms. The 3,043 declarations under 5 ms sum to
  5.7 s; only 17 exceed 50 ms (1.4 s together). No family (numeric segments
  of the generated name folded) is above 0.9 s.
- Phases over the certificate: kernel gate 47 %, `decl_type` 26 %,
  `decl_body` 19 %, `decl_emit` 3 %. The certificate is written as `.hthr`
  source and elaborated like any module (`crates/cli/src/native.rs`,
  `elab_module_source`), so about 45 % is the frontend re-deriving what the
  generator already knew. `decl_type`/`decl_body` are self time: unify,
  resolve, whnf and matching are their own columns and are small here, so the
  bulk is not attributed below the declaration yet.
- The per-byte fact families are ~840 declarations, ~2.1 s: `byte_present`,
  `byte_page`, `byte_found`, `byte_offset` (167 each), `code_drop` (168) —
  one small theorem per instruction byte.

Why it matters: this is what every `build-x86` pays and the suite pays per
build — the native test binaries are the heaviest rows of the full lane, and
`native_stack_save` alone is two builds of one program. The library's x86
modules are paid once per compiler build (images), the certificate never is.

Two levers, independent:

1. **Fewer, larger generated declarations** (generator side): e.g. one fact
   per instruction instead of per byte, where the proof shape allows it. Cuts
   both halves of the constant. Natural to do alongside the next x86 feature
   round if it changes the per-byte shape anyway.
2. **What a trivial generated declaration costs the frontend**: attribute
   `decl_type`/`decl_body` for one of the 1–2 ms items (`--only` does not
   reach a generated certificate; probe by writing the certificate out and
   checking it with `--timings`, or bracket more of the declaration path).
   A fixed per-declaration price in the frontend is a tax on every generated
   module, not only this one.

Trigger: the x86 feature line growing the certificate (more instructions,
calls) — the constant multiplies by declaration count. Danger: do not trade
readable certificate source for speed without asking; the `.hthr` certificate
is a deliberate artifact.

Related: [[function-ir-x86-proof-scaling]] (the earlier per-family rounds on
this workload), [[frontend-large-proof-composition-cost]].

## Log

- 2026-10-03: **Re-attributed on the filter stack (2026-10-03, cold `build-x86` of `examples/x86-native/wc.hthr`, width one, `scripts/perf ab` raw tables).** The shape this issue describes moved:

  | share of item time | before [[goal-world-copies-psi]] | after |
  |---|---|---|
  | the program's own proofs (`wc` module, 27 decls) | 39% | 12% |
  | the `Fields` formatter's two certificates (15.7k decls) | 32% | 47% |
  | bundled library (3.4k decls) | 23% | 32% |
  | the step piece (2.5k decls) | 5% | 8% |
  | the process certificate (333 decls) | 1% | 1% |

  - The per-byte fetch families this issue names do not exist on the read profile: `read_filter.rs` states residency once (`x86_64_fetched_code`, `CodeResident`), and the whole process certificate is 333 declarations, ~1% of a build. They remain in `native/calls.rs` and `native/elf.rs` (the call and fixed-input profiles, `reused_callee`), which no program on the filter line uses; lever 1 as written is now a lever for those profiles only.
  - The largest single line was not the certificate at all: the program's four `split_all; all_goals { omega }` proofs plus `Filter`'s default `advances` field, 39%, almost all frontend self time, and ~4x what the same declarations cost under `heather check` with identical counters. Cause and fix: [[goal-world-copies-psi]] (−29% on the whole build).
  - What is left with the per-declaration shape is the formatter: 15.7k generated declarations at a few ms each, 43% frontend self time (`decl_type`/`decl_body`) and 31% gate, no family above ~12% of it (`*_preserves`, `*_carry`, `*_instructions_#`, `*_correct`, `*_decodes`). Its certificates are checked before any program module and keyed per profile, so an image store pays them once for every `Fields` program; a cold store (or a compiler change in the suite) pays them on the first. That is where lever 1 ("fewer, larger generated declarations") now applies — to `function_ir_x86_lower/structured_cert.rs`'s per-node families, not to fetch facts.
- 2026-10-03: What the full `wc` command adds: docs/native-wc-command-design.md §9. It removes the `%7d` certificates, 47% of a cold build, and adds about 630 library declarations. The cold build comes to about 70–80% of today's.
- 2026-10-03: **The formatter's certificates were not a flat constant after all.** Attributed per declaration on a cold `wc` build, half the formatter's time was its top thousand declarations, in a few families: `_preserves` re-evaluating the machine state once per register, a quadratic inline `at_width` in every `_carry`, and declarations nothing read (the leaves' execution chains and artifacts, inner nodes' `_artifact`/`_rip`). Cut in [[structured-certificate-cost]]: standalone `field_low` 45 s → 25 s, `field_high` 59 s → 36 s. What is left is one conversion per node per family; this issue's per-declaration framing now applies only to the call and fixed-input profiles.
