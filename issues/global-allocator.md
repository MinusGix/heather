---
title: Link a size-class allocator above the kernel (mimalloc)
status: closed
labels: [performance,tooling,dependencies]
area: infrastructure
created: 2026-11-09
updated: 2026-11-10
---

Checking is allocation-bound: kernel terms are `Arc` trees built node by
node, substitution rebuilds the spine above every change, and the
elaborator's tables are maps of small boxed values. Stack samples of a cold
check put glibc `malloc`/`free` and the drop glue feeding them on every hot
path, and no single call site owns the cost, so the allocator itself was
the cheapest lever to try.

## What landed (2026-11-09)

`#[global_allocator] static ALLOC: mimalloc::MiMalloc` in
`crates/elab/src/lib.rs`, so every binary that links the elaborator (the
`heather` CLI, the test and bench binaries that drive it in process) uses
it. The dependency is declared in `crates/elab-lib` and `crates/elab-unit`,
which compile that source; `libmimalloc-sys` builds at opt-level 3 in the
dev profile. No `unsafe` is written for it.

The kernel's dependency list is unchanged ([[dependency-policy]]): a kernel
linked alone (its own tests, `scripts/bench`'s kernel benches) keeps the
system allocator, and an allocator implements no judgment.

## Which allocator

Measured by `LD_PRELOAD` first, so no build was needed to compare (Log). The
three candidates land within noise of each other and all well clear of
glibc; mimalloc was taken because its crate builds from vendored C with `cc`
alone in a few seconds, where jemalloc's runs `configure` and `make` on
every cold build ([[fresh-container-compile-cost]]).

## What it costs

- Peak RSS rises about a tenth (size-segregated pages hold more slack).
- A cold build compiles one more small C library.
- Address-space reservations are larger than glibc's; the suite's 6 GiB
  per-process rail and the 8 GiB direct-run rail both hold.

## Log

- 2026-11-09: `LD_PRELOAD` comparison, cloud box, cold width-one `heather check docs/showcase/calc_parser.hthr`, single runs. On master 8a593b6: glibc 106-109 s, mimalloc 84 s, jemalloc 79 s, tcmalloc 85 s. After [[empty-substitution-tail-decoration]] (two runs each): glibc 37.4/37.9 s, mimalloc 31.9/33.0 s, jemalloc 31.8/32.7 s. Linked in, `scripts/perf ab`, three interleaved samples, same file: wall 35.4/32.6/31.3 s to 28.3/27.2/25.9 s (-16%, separate), kernel gate 11.2/10.1/9.9 s to 9.2/8.8/8.3 s (-14%), max RSS 570 MB to 637 MB (+12%), 43 counters identical. At the default eight kernel workers, single runs: 24.1 s to 19.3 s.
- 2026-11-09: Fixed cost, from the same corpus A/B as [[empty-substitution-tail-decoration]]'s last entry: a small process pays about 55-60 MB of peak RSS for the allocator's initial pages (`nat.hthr` 113 MB to 171 MB, `omega.hthr` 172 MB to 227 MB, `calc_parser` alone 570 MB to 637 MB). It is a constant, not a proportion, so it vanishes on the certificates (3.1 GB to 1.6 GB with both changes) and is the thing to look at if many small children ever run at once under a tight memory budget.
- 2026-11-10: Two things about the linked allocator the preload comparison could not show, both measured on the cloud box over the stack at [[free-variable-bounds-in-the-node]]. **(1) Every Rust allocation takes mimalloc's aligned entry, and mimalloc 3's fallback over-allocates.** The `mimalloc` crate's `GlobalAlloc` calls `mi_malloc_aligned` for every request. v3 serves it from the size class's free list when there is a block, and otherwise takes the ordinary path only for a size it calls naturally aligned, a power of two (`alloc-aligned.c`, `mi_malloc_is_naturally_aligned`; v2 also accepts any alignment up to 16, which is all `malloc` promises anyway). Everything else is over-allocated by the alignment into the next class up. On a cold showcase check, 13.5 M of 51 M allocations took that path: 4.6% of the run's instructions. A 60-line `GlobalAlloc` of our own that calls plain `mi_malloc` for alignments up to two words (what std's `System` does over libc) removes it: 46,884 M instructions to 44,772 M. **It buys nothing that matters**: `scripts/perf ab`, five interleaved samples, wall 14.98 / 13.97 / 13.93 / 14.68 / 13.75 s against 14.76 / 14.10 / 14.21 / 15.09 / 14.53 s (no result), peak resident no change. Not adopted: it would be the workspace's second crate with `unsafe` for no seconds. **(2) The `v2` feature of the crate is a constant 26 to 35 MB of peak resident memory per process cheaper, and no faster.** `lib/std/num/nat.hthr` 64 MB to 38 MB; the showcase, five samples, 432 to 458 MB against 406 to 413 MB at width one (−8.9%, separate) and −3.6% at eight workers; the x86 certificate 1008 MB to 976 MB; wall no result on the showcase at either width. This is the fixed cost the entry above names. One line in `crates/elab-lib/Cargo.toml` and `crates/elab-unit/Cargo.toml` (`features = ["v2"]`), no `unsafe`; not switched here because it changes every process's memory behaviour under the suite's address-space rails and deserves its own exact-lane run. Instructions with v2: 45,455 M.
