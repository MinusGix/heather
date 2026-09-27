---
title: The native print test runs within 6% of the CPU rail under suite load
status: open
labels: [x86,testing,performance]
created: 2026-09-25
updated: 2026-09-27
---

`wc_l_prints_every_line`, formerly `wc_l_prints_what_the_read_returned` (`crates/cli/tests/native_read_loop.rs`)
spawns one `build-x86 --read-loop --print` under `scripts/test`'s
`ulimit -t 300`. Alone, cold and at width one it costs about 245 CPU-s
(2026-09-25). In the full suite that landed it (f86941e5) the test took
**283 s**. The binary's three tests together were 377 CPU-s, and the print
build's child sat within about 6% of the rail. This is
[[native-summary-test-cpu-margin]]'s failure mode again: a gate that passes or
fails on host load is not a gate. It is skipped by the fast lane, so the full
lane is where it will tip.

Most of the cost is library, not the certificate:
- `decimal_line` is about 75 s, mostly `omega`
  ([[omega-div-mod-goal-cost]], [[nat-div-mod-lemma-kit]]);
- the call profile's image and fits lemmas are about 16 s;
- `elf64_read_loop`, the loop trace and the fetched bridge are about 10 s.

## Options, in preference order

1. Shrink `decimal_line` by the two issues above. That is the real fix and
   helps every future printing program.
2. Warm the library image before the test, as `native_warmup` does for the
   native prefix. The child then replays `decimal_line` and `elf64_read_print`
   (kernel-rechecked) instead of elaborating them. This moves the cost out of
   the rail and does not reduce it.
3. Split the build across two children: the format artifacts, then the
   process.

Do not raise the rail or shrink the example (the same rule as the issue
above).

## Acceptance

- The print test runs at least 30% under the rail in a full suite run, and
  the margin is recorded in this issue's log.

## Log

- 2026-09-25: Measured in [[nat-div-mod-lemma-kit]]'s full suite: `wc_l_prints_what_the_read_returned` took 170 s under suite load, down from 283 s. `decimal_line` went from 106 to 32 CPU-s standalone at width eight, and nothing in it sends a `div`/`mod` goal to `omega` any more. Option 1 above is done for `decimal_line`. Whether the rest now leaves enough margin is this issue's call.
- 2026-09-25: It tipped. In the full suite after the crossing-link fix, the print build's child was SIGKILLed at 369 s wall. The fix changed the formatter certificate's terms, so the verdict store at `target/native-test-images` was cold for them, and the child ran beside heavy parallel targets. A fresh print build alone at width one costs 239 CPU-s, the same as before the fix, so the change did not make it slower. With a warm verdict store the whole `native_read_loop` target takes 6 s: the cost is almost all first-time kernel checking of terms that changed. The test is therefore safe except in rounds that change what the generator or elaborator emits, and those are exactly when the gate has to run. Option 2 above (warm the read-loop/print bundle before the test) would pre-check the library half, but not the generated certificate. Still open. The acceptance margin was not met in this run.
- 2026-09-27: 2026-09-27: The print test is now `wc_l_prints_every_line` (read until end of file, [[native-read-until-eof]]). The fast lane skips it under the new name. Its build now includes the outer loop's proofs, and a 9999-line input takes three reads.
