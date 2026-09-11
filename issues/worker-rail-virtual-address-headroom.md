---
title: Eight kernel workers under the 6 GiB address-space rail: one unreproduced allocation failure at ~2 GB RSS
status: open
labels: [testing,elaboration,parallelism,memory,robustness]
created: 2026-09-11
updated: 2026-09-11
---

During the verdict-reuse round (2026-09-11) one pass of the heather-cli certificate unit tests died with \`memory allocation of 144 bytes failed\` under \`ulimit -v 6291456\` while its resident set was ~2 GB. Five later passes, three after a memory fix that retires recorded bindings as the replay consumes them, were clean at 2.05 GB RSS. Not reproduced, not understood.

The rail is *virtual address space*, not RSS. Things that reserve address space without touching it: eight worker threads at \`RUST_MIN_STACK\` (8 MiB each, plus libtest's), per-worker value arenas and \`BodyCache\`s, and glibc's per-thread malloc arenas (up to 8 × cores, each reserving 64 MiB of address space on first use — with 16+ threads that alone can be several GiB of VA). A 144-byte allocation failing at 2 GB RSS is the signature of exhausted *address space*, most plausibly malloc arena reservation, not of exhausted memory.

To do when it recurs (or to rule it out now): run the target with \`MALLOC_ARENA_MAX=2\` (or 4) and compare VmPeak from \`/proc/self/status\` at exit against RSS; if VA is the issue, set \`MALLOC_ARENA_MAX\` in scripts/test and the runner (cheap, and it also reduces fragmentation), and record VmPeak in the timings run row so the headroom is visible.

## What it assumes from elsewhere
- **[[parallel-kernel-gate]]** owns the workers. Assumed here: eight workers is the default that made this reachable.
- **[[kernel-arena-terms-frozen-prefix]]** owns the long-term memory story. Assumed here: nothing; this is a rail-accounting question.
