---
title: linux_wp dies at the 300 CPU-s rail when the semantic image store is cold
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-10-22
updated: 2026-10-22
---

On a fresh 4-CPU cloud container, a full `scripts/test` reports `INCOMPLETE`:
`crates/elab/tests/linux_wp.rs` (its one test,
`the_io_loop_reads_to_the_end_and_exits`) is SIGKILLed at the 300 CPU-s
rail. Seen 2026-10-22 on master b04c174 and on the
[[fresh-container-compile-cost]] branch, both with `target/semantic-test-images`
and `target/decl-cache` empty. Run again with the stores warm, it passes in
193 s on both, and `linux_spec.rs` / `linux_wp_count.rs` sit at 81–94% of the
rail in the same cold runs.

So every fresh container's first full run is red until a second run, and the
cold margin of the native Wp tests is gone. Levers, unexamined: the cold path
is the shared x86 prefix images built inside the test rather than by the
warmup (`semantic_x86_warmup` may not cover the Linux modules), or the
module's own elaboration cost ([[native-one-wp]], whose syscall pass costs
elaborator whnf).

## Log

- 2026-10-22: Filed from the fresh-container compile round.
