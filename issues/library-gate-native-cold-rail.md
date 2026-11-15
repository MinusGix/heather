---
title: Keep the library gate's native and tactic children, and write-elf, under the CPU rail from a cold store
status: closed
labels: [testing,caching,performance,images]
area: infrastructure
created: 2026-10-27
updated: 2026-10-27
---

On master at 92525ef, a suite run whose nat/int/rat edits invalidated the
image store had library-gate children killed at the 300 s CPU rail
(`lib/native` and `lib/_tests/native` at about 310 CPU-s in the cloud, seen
on #222 and #224; `lib/_tests/std/tactic` at about 395), and so were
`native_cat.rs`'s two `write-elf` tests and
`native_tools.rs::compiled_head_runs_as_gnu_head`. Warm, all of them pass.

## Causes

Measured on a 4-CPU cloud box with the dev binary the suite runs, one kernel
worker, `--timings`.

1. **Module images were trees.** `module_image::put_term` wrote every
   occurrence of a subterm, though the elaborator's terms share subterms
   freely. The tactic modules' images were about 110 MB (`tactic`), and
   `native_build`'s 133 MB. Every gate child whose world prefix passes the
   tactic family decoded them: in `lib/native`'s child, `image_decode_ns`
   was 33 s of 278 (tactic 15.3 s and 2.4 GB of peak growth, norm_num 7.9 s,
   interval_tactic 4.0 s, norm_num_real 2.6 s) plus about 25 s of system
   time paging that memory; `lib/_tests/native` was 62 CPU-s of which its
   own items were 4. See [[image-tree-walks-let-shared-terms]], which
   predicted this for let-shared proofs.
2. **`write-elf` and the CLI warmup loaded closures in their own order.**
   A module's image is keyed by everything loaded before it
   (`docs/archive/library-world-design.md` §1), so `write-elf` of cat and of a
   tool (`native_tools.hthr`, whose closure is cat's reached through
   `native_build` first) shared almost no image with each other or with
   the gate. Each was one process elaborating its whole closure cold: cat's
   warmup 274 CPU-s and head's `write-elf` 257 on master.

## What changed

- Images are DAGs (`docs/semantic-module-images-design.md`, Stage 4a): a
  term or type is written once and later occurrences of an equal one are a
  back-reference, numbered by structure so the bytes stay a function of the
  terms. Format bumped.
- `write-elf --world <dir>` loads the world's prefix first, as `check
  --world` does. `native_cat.rs` and `native_tools.rs` pass `--world lib`,
  and `scripts/test`'s `cli_images_warmup` is now the library gate itself,
  which builds the world a folder per child.

## Measurements (cold store, same box)

| | master | this change |
|---|---|---|
| `lib/std` alone, one process | 509 | 536 (writer numbers nodes; partly noise) |
| `lib/native` after `lib/std` | 278 | 198 |
| `lib/_tests/native` after both | 62 | 9 |
| `lib/_tests/std/tactic` after `lib/std` | | 75 (tactic decodes in 0.3 s) |
| image store for `lib/std` | ~390 MB | 31 MB |
| cat warmup / cat `write-elf` / head `write-elf`, own order | 274 / 29 / 257 | 262 / 25 / 250 |
| cat / head `write-elf` over the gate's world store | | 23 / 23 |

The real gate (`scripts/test --test library`, cold, three children at a
time, each child timed) on the same box:

- **master fails**, and on memory before CPU: `lib/_tests/std/tactic` was
  killed by the container's OOM killer at 5.2 GB resident after 89 CPU-s,
  and `lib/native` aborted on the 6 GiB address-space rail
  (`memory allocation of 88 bytes failed`) after 25. Three children each
  decoding the tactic family's tree images is what the box could not hold.
- **with the change it passes**: largest child `lib/_tests/std/num` 135
  CPU-s, `lib/_tests/native` 129 (it built most of `lib/native`'s modules,
  racing that folder's child for them), `lib/std/tactic` 101,
  `lib/_tests/std/tactic` 92, `lib/native` 65; children sum to 769, and no
  child's system time is above 4 s (master's were 8–12).

## Left

- The merkle walk is still a tree walk (`merkle_walk_ns` 5–7 s in the
  native children); making it linear changes the hash definition, so it is
  [[image-tree-walks-let-shared-terms]]'s remaining half.
- The writer numbers every node of every encoding (image, interface,
  slices) from scratch: a cold `lib/std` pays about 2% more for it.

## Log

- 2026-10-27: Filed and closed in one round (this file).
