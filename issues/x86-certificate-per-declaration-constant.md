---
title: The x86 call certificate costs a per-declaration constant, half of it the frontend re-elaborating generated source
status: open
labels: [x86,performance,elaboration,compiler]
created: 2026-09-23
updated: 2026-09-23
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
