---
title: The module-image decoder's depth budget is not sized to the stack it runs on
status: closed
labels: [cache, robustness]
code: crates/elab/src/module_image.rs:304 @ 1334d9a9
created: 2026-09-29
updated: 2026-09-29
---

`Reader::node` refuses a term deeper than `ModuleImageLimits::max_depth`
(2048), and decodes recursively below it. On the 8 MiB main thread that is
not stack-safe: replaying the `wc` certificate's image (its loop's published
bytes are a right spine of a few hundred appends, several term nodes each)
overflowed the stack at about 1500 frames in the test profile's `heather`
(`thread 'main' has overflowed its stack`, SIGABRT), while the cold build
that wrote the image passed. Release builds have smaller frames and passed.

Found in [[native-wc]] slice D (2026-09-29). Worked around in
`crates/cli/src/native.rs` (`on_deep_stack`): `build-x86` and `compile-x86`
now run on a thread with a 256 MiB stack. `heather check --cache` still
decodes on the main thread and has the same exposure.

Shape of a fix: either size the budget from a measured per-level frame cost
and the stack actually available, or decode terms iteratively (an explicit
stack), as the kernel's deep traversals already avoid native recursion past
their own budget ([[kernel-native-depth-budget]]).

## Log

- 2026-09-29: Fixed by sizing the stack from the budget, not the budget from the stack.
  The decoder keeps its recursion but runs on a thread of its own:
  `decode_on_own_stack` spawns one with `max_depth × DECODE_FRAME_BYTES`
  (4 KiB) plus 1 MiB, for `decode_delta` and `relocate_events`. If the OS
  refuses the thread, the result is `ModuleImageDecodeError::NoStack`, a load
  refusal; decoding does not fall back to the caller's stack. The depth budget
  now holds on any caller's stack, `heather check --cache` included, so
  `native.rs`'s 256 MiB build thread is gone.

  The measurement changed the fix. Probing each recursive path with a
  test-only low-water mark in `Reader::node` found that a kernel term level
  cost 16 KiB of stack in the test profile (8 MiB held only about 500 levels),
  against about 1–2.5 KiB for surface syntax. The cause was `get_term`'s one
  large match: with the children decoded inline, every arm's fields had stack
  of their own. Decoding children out of line (`term_rc`/`type_rc`,
  `#[inline(never)]`) brought a term level to 2.2 KiB. The deepest shape is now
  a block's `let` at 2.5 KiB. The writer was never the problem: at most
  224 bytes a level.

  Pinned by `every_nesting_level_fits_the_decoders_frame_bound` (eight spines
  at the budget, each level within `DECODE_FRAME_BYTES`) and
  `the_depth_budget_holds_on_a_small_callers_stack` (every spine decodes at the
  budget from a 256 KiB caller and is refused one level past it). Negative
  control: decoding on the caller's stack makes the second test abort with a
  stack overflow. `native_wc` passed cold (100 s) and then warm (11 s): the
  warm run replays the certificate's images on the 8 MiB main thread without
  the workaround.

  The writer still publishes an image deeper than the budget, which the
  reader then refuses at every load. That residue is filed as
  [[module-image-writer-ignores-depth-budget]].
