---
title: Cut what every process over the native world pays before its own work
status: open
labels: [performance,caching,images,native,tests]
area: infrastructure
milestone: [hih-tools]
created: 2026-10-29
updated: 2026-10-29
---

Every native test spawns `heather write-elf`, and every one of those
processes loads the native world (the library up to `native_tools`) from the
image store before it reads its tool. Measured on a 4-CPU cloud box with the
dev binary the suite runs, at kernel width one (`perf/bench/targets.md`, T1):

- **A warm `write-elf`, with nothing left to kernel-check, is not cheap.**
  The second `write-elf` of `yes_tool` over the same store, with the
  certificate's verdicts stored, ran with zero kernel time. About half of it
  was the merkle walk and about a third was `image_recheck`. The rest was
  decode and `write-elf`'s own reads. The cold run of the same tool was about
  twice the warm one, and the certificate's kernel check was under a tenth of
  the cold run.
- **Where the merkle walk goes, warm:** the replayed certificate module, the
  first declaration of `write-elf`'s in-memory probe module (`<p>_a_0`, a
  one-line `fn`, seconds of walk in both the probe and the certificate), and
  `native_build_parts`. The walk is still a tree walk
  ([[image-tree-walks-let-shared-terms]]). A one-line declaration costing
  seconds suggests the first declaration of a fresh module pays for hashing
  its prefix.
- **Where `image_recheck` goes, warm:** the `native_compile_*` modules,
  hundreds of thousands of evaluator steps each, with every verdict present.
  `replay_module_delta` re-runs `check_global_binding_statement` for every
  binding the gate does not admit. Worth reading which bindings those are
  (statements, sealed proofs, theorems whose gate key is built with `opaque:
  false` in `recheck_extension`).
- **The first `write-elf` after the library gate misses `native_build_parts`
  and `native_tools`.** It re-elaborates them (relocation, merkle walk and
  decl body together, about ten seconds), and the second run hits. The gate's
  `lib/native` child and `write-elf --world lib` key these modules
  differently. In the suite this is paid at least once per store, and once
  per concurrent native test that gets there first.

A `heather check` of a one-line root that imports `native_tools`, warm, pays
the same floor without `write-elf`'s parts (`native/world-replay`).

## Cases

`scripts/bench-probes --filter native/world-replay`, `native/elf-floor-yes`
(and `native/elf-cold-yes` with `--heavy` for the cold total).

## Done when

The warm `write-elf` floor is dominated by the tool's own work, and
`write-elf` after the gate hits every library module. Both are read off
those cases.
