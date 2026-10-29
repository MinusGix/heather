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

## Log

- 2026-10-29: Two of the three costs fixed (branch claude/project-thread-fod7fz).
  - **`image_recheck` was theorem statements.** Replay asked the gate about
    every definition, but a declaration without a body had no key, so its
    statement was re-checked on every load: in the warm native world, 2916
    unsealed and 731 sealed statements, all of the replay's evaluator steps.
    Statement verdicts now cover them (`KernelGate::admits_statement`,
    `merkle::statement_key`, `docs/cache-v1-design.md` §12). A statement
    check that opened a sealed proof keeps none.
  - **Most of the merkle walk was the world hashed again.** `write-elf`'s
    forks share the parent's gate, and the gate cleared its prefix of
    interface hashes whenever a shorter Ψ asked, so the first probe
    declaration and the certificate each re-hashed the whole world. The gate
    now keeps what the asking Ψ shares with the last (`GlobalMark`,
    `GlobalBindings::common_prefix`). The same change closes a hazard the old
    rule had: a divergent Ψ already longer than the prefix inherited its
    hashes (`a_longer_divergent_psi_does_not_inherit_the_last_ones_hashes`).
  - One sample each, cloud: `native/world-replay` 9.5 to 4.8 CPU-s (image
    6.7 to 1.7, evaluator steps 2.1M to 123); `native/elf-floor-yes` 20.0 to
    8.0 (merkle 8.7 to 2.8, image 8.0 to 2.0). Three-sample rows are in
    `perf/bench/results.tsv`.
  - **Left: the first `write-elf` after the gate.** `native_tools` and
    `native_build_parts` are imported by no library module, so they are not
    in the world (`crates/cli/src/world.rs`): each process loads them after
    its own prefix, and the gate's `lib/native` child and `write-elf` have
    different prefixes, hence different keys. The key's build lock means the
    suite pays this once per store, not once per process. Two ways to fix
    it: a `lib/_tests` probe module that imports them makes them shared, or
    `write-elf` loads its closure after the gate's prefix for the source's
    folder. Not done here.
  - What is left of the warm floor: the world's one interface walk (about
    1.6 s, in `world-replay` too), decode, and `write-elf`'s own reads
    (930K evaluator steps).
