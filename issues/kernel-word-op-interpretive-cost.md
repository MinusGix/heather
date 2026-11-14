---
title: A closed u64 operation costs 80-270 evaluator steps around one native run
status: open
labels: [kernel,performance,bitvectors]
area: kernel
created: 2026-11-14
updated: 2026-11-14
---

Closed verdicts over `u64` code (the scanner's `token_kinds_spelled_*`,
`runtime fn` probes, native certificates) run in the kernel's evaluator at
a roughly constant time per step, and a word operation costs 80 (`eq_bit`)
to 270 (`add`) steps even though the operation itself is one native
transducer run. After [[native-word-fuel-per-word]] those steps are real
work: a per-op constant of interpretation around a native core.

## Where the steps go

Measured 2026-11-14 with per-call-site `spend` counters (a throwaway
patch) over twelve rows of `TokenKind::spelled`, about 240K steps:

- β (`step_fire`, `Lam`/`App`): ~28%. The wrappers each op passes through
  (`unsigned_lt_bit` → `borrow_sub_bit` → `borrow_bits` → the
  `match n as λ …` applied to its arguments), each with `{n}` and `self`.
- δ-unfolds (`delta_step`): ~11%.
- Type decoding (`El` of a `Vec` code, `vec_ty`): ~8% — types are forced
  inside a closed Bool computation.
- `BitRun` unpacks and pair projections: ~6% — something reads words one
  bit at a time outside the transducers.
- The per-bit fuel charge: ~34% (now one unit per run).

perf over the same work shows no hotspot: `drive_above` ~9%, then arena
allocation, substitution and drops.

`shift_right(x, k)` is `k` single-bit shifts (a recursion on the count,
which the transducer class declines): `scan_accept` is eight word ops a
byte, `scan_family` three.

## Directions

- Find what forces `Vec` types and unpacks bits in a closed word
  computation (the counters are cheap to re-add around `spend`).
- A shift by a closed count as one run.
- Fewer steps per call of a small closed wrapper (δ+β of a definition
  whose body is an application of another), without matching definition
  shapes (`issues/kernel-acceleration-policy.md`).
