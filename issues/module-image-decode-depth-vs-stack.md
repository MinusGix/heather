---
title: The module-image decoder's depth budget is not sized to the stack it runs on
status: open
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
