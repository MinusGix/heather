---
title: The elab rebuild floor: a second O3 compile for unit tests and a 22 s lib rebuild per edit
status: open
labels: [testing,performance,build]
created: 2026-09-24
updated: 2026-09-24
---

What remains of a Rust edit's build once
[[elab-unit-tests-wait-on-cli-dev-dependency]] lets the unit-test compile run
in parallel ([[rust-edit-loop-build-bound]] owns the numbers):

- elab's unit-test compile, a second full O3 compile of the crate under
  `cfg(test)`, ~40 s: the floor of the build's wall.
- the elab lib rebuild, ~22 s at `opt-level = 3`, for any edit to elab *or*
  the kernel.

Levers, not yet costed: move unit tests that use only the public API out of
`src/` (shrinks the second compile); split `heather-elab` into smaller crates
(the only lever that also shrinks the lib rebuild); reconsider elab's dev
`opt-level = 3`, which trades against test runtime and needs a
`scripts/perf ab`-style comparison of the loop, not of the tests alone.

Re-measure after the first lever lands before choosing.
