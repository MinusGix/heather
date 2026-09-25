---
title: The native print test runs within 6% of the CPU rail under suite load
status: open
labels: [x86,testing,performance]
created: 2026-09-25
updated: 2026-09-25
---

`wc_l_prints_what_the_read_returned` (`crates/cli/tests/native_read_loop.rs`)
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
