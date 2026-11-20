---
title: linux_wp dies at the 300 CPU-s rail when the semantic image store is cold
status: closed
labels: [testing,performance]
area: infrastructure
created: 2026-10-22
updated: 2026-11-20
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
- 2026-10-22: **Made cheaper rather than given more rail.** Measured on a
  4-CPU cloud box, each target alone at width one: cold (image and verdict
  stores empty), `linux_wp` was 342 CPU-s, of which ~220 s was the shared
  Linux prefix every such test process builds for itself when the store is
  cold, and warm it was 121 s, all of it `drain_pass`. What was expensive, and
  what changed:
  - Four library proofs matched a trace witness inside a λ whose type is
    `IsTrace` of a tree's call: `ITree::implements_sized` (5.76M kernel steps),
    `sim_vis` (3.65M), `stream_filter_spec::filter_sends` (7.74M; 80 s of the
    `linux_spec` cold run), `wp_next_runs` (1.1M). Each call arm is now a
    lemma taking the witness as a `VisTrace` parameter, about 1 s apiece. Why
    the in-place form costs so much is open:
    [[trace-match-under-computed-binder-cost]].
  - `Prog::no_holes_fit` spent 20 s in the elaborator: its seventeen
    recursive calls each reduced their expected type in
    `ctor_here_expected`, whose "only constructors are visible" test holds
    vacuously of a name nothing has registered yet (the declaration being
    checked). It now stands down unless some inductive registered the name;
    1.3 s.
  - `drain_pass` spent ~90 s in `absurd(no)`, which reduced the jump flag off
    the answered machine state by substitution. The fixture cites a lemma
    (`drain_none_zero`) as its other two answers did; 22 s. The elaborator
    cost: [[absurd-reduces-computed-sides-by-substitution]].
  After: `linux_wp` 118 CPU-s cold and 32 s warm; `linux_wp_count` 105 s
  cold alone (prefix plus its three elaborations of the control);
  `linux_spec` 138 s cold alone including the whole x86 prefix the suite's
  warmup otherwise builds first. Kernel counts of the unchanged items are
  unchanged.
- 2026-10-23: **Checked on a fresh box after the fix: no longer reproduces.**
  The failing reports all predate PR #133. On a fresh 4-CPU cloud container
  at master 1ae5dd6 (#149), with `target/semantic-test-images`,
  `target/decl-cache` and the runner's timing history all absent, a full
  `scripts/test` passed (3698 passed), with `linux_wp` at 142 CPU-s of the
  300 s rail, `linux_wp_count` 129 and `linux_spec` 56. A second run on the
  same box, with the stores warm, gave 48, 34 and 6. So about 95 CPU-s of
  `linux_wp`'s cold run is the Linux prefix it builds for itself, and the
  warmup does not cover that prefix (`semantic_x86_warmup` stops at
  `x86_64`). The cold margin is about half the rail. If it shrinks again,
  the lever is a warmup over `READ_LOOP` and the Linux list, not more rail.
- 2026-11-20: 2026-11-20: The same shape in `linux_determinism`, still open: [[linux-determinism-cold-rail]].
