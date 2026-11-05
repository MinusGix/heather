---
title: Module images and the merkle walk treat a let-shared term as a tree
status: open
labels: [caching,performance,images]
area: infrastructure
created: 2026-10-26
updated: 2026-10-27
---

Found while measuring [[rewrite-setoid-relations]]: a theorem whose statement
is a k-let chain with each link used twice (`let vᵢ = g(vᵢ₋₁, vᵢ₋₁)`, the
`rewrite/let-addr0` shape) checks in time linear in k, but `heather check
--cache` on it is exponential: at 16 lets the declaration's own work was tens
of milliseconds while its merkle walk took seconds, and the run's image
publish and relocation took most of the rest; at 32 lets the run passed five
minutes. Without `--cache` the same file checks in milliseconds.

`docs/mengine-survey.md` §3.3 predicted this ("`put_term` writes a tree") and
left it as a note until an image was measured tree-blown. This is that
measurement, on a generated file rather than the library, so it is not urgent
for the library as it is, but it is the next wall for let-heavy proofs now
that the elaborator and the kernel share such terms.

Wanted: the merkle walk, the image writer (`put_term`) and relocation keep a
per-node memo (the hash of a shared node computed once; a shared node written
once and referenced), so their cost is the term's shared size. Reproduce with
the `rewrite/setoid-let-addr0` source at 16 lets under `--cache --timings`
and read `merkle_walk_ns`, `image_publish_ns`, `image_relocate_ns`.

## Log

- 2026-10-27: Images half done 2026-10-27 ([[library-gate-native-cold-rail]]): `put_term`/`put_type` write each structurally distinct node once and back-reference repeats, and the reader returns the shared `Arc`; relocation goes through the same codec. The merkle walk is still a tree walk.
- 2026-10-29: Seen in the native tools' fixed cost ([[native-process-fixed-cost]]): in a fully warm `write-elf yes_tool` the merkle walk was about half the run, several seconds of it on a one-line `fn` that opens write-elf's probe module. Probe cases `native/elf-floor-yes` and `native/world-replay` (`scripts/bench-probes`).
- 2026-11-05: gardener: cites a file it shares with [[open-payload-shift-copies]] (`docs/mengine-survey.md`).
