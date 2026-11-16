---
title: Elaborate opaque proof bodies on the worker threads
status: open
labels: [performance,elab,design]
area: language
created: 2026-11-11
updated: 2026-11-11
---

Only the kernel gate runs on the worker threads, so a cold check is bounded by the serial elaborator however many cores there are. Found while writing [[performance-overview-2026-11-11]]; the gate's own design is `docs/kernel/parallel-kernel-gate-design.md`.

## Measured

2026-11-11, four-core cloud box, release binary at #553 plus the name-record fix:

- `docs/showcase/calc_parser.hthr` cold, plain: 11.1 s at width one, 9.1 s at the default eight workers. The gate is 36% of the attributed time at width one.
- `lib/std/analysis/closed_interval.hthr` cold with `--timings`: 88.3 s at width one, 77.1 s at eight workers. At eight workers the main thread's `decl_body` is 24.6 s and `resolve` 16.6 s.
- Over the whole library at width one: gate 37%, declaration bodies 22%, everything else 41%.
- `--build-jobs 4` does not help a single file: the showcase takes 13.9 s with it, because its closure is mostly a chain and each child replays its prefix ([[build-children-replay-their-imports]]).

## The idea

A theorem's body is opaque to every later declaration: once its statement is committed, nothing downstream can observe how the proof was found. So the body can be elaborated, and then gated, off the main thread, the way the gate already is. The main thread would elaborate statements and the bodies of transparent definitions only. On the library's numbers that moves the parallel share of a cold check from about 37% to about 60%.

What it needs, as far as I can see without having tried:

- an elaborator that can run a body against a frozen view of the world at the statement's commit (`fork_over` and the module-pass checkpoint are the existing pieces);
- generated declarations a body mints (instances, gendefs, open derivations) to land deterministically, in source order, whatever order the workers finish in;
- errors and warnings reported in source order, and the serial fallback the parallel gate already has;
- tactics and host requests that are safe off the main thread.

This is a design round before it is an implementation one.

## Done when

A design note says whether the frozen-view elaboration is sound for every declaration kind that has an opaque body, with a prototype's timing on `closed_interval.hthr`.
