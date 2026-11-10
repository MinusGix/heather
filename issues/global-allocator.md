---
title: Link a size-class allocator above the kernel (mimalloc)
status: closed
labels: [performance,tooling,dependencies]
area: infrastructure
created: 2026-11-09
updated: 2026-11-09
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
