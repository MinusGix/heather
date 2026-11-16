---
title: Development resource limits as a `heather` flag, not a shell `ulimit`
status: open
labels: [tooling, cli]
area: infrastructure
created: 2026-11-15
updated: 2026-11-15
---

The rails that keep a development run from taking the whole machine
(CLAUDE.md: 8 GiB of address space, 120 CPU-s, no core) were a shell
`ulimit` written around every command. That put `ulimit` into commands meant
for users, who need none of it (Minus, 2026-11-15: "ulimits are primarily
for avoiding devtime being problematic … possibly we should include
something like that in the language itself, but as a flag, but it shouldn't
be in the command line").

## Built (2026-11-15)

`--limits <spec>` on every subcommand, and `HEATHER_LIMITS` in the
environment (`crates/cli/src/limits.rs`). Off unless asked for. `dev` is
the CLAUDE.md rail; `memory=<size>`, `cpu=<seconds>`, `core=<size>` and
`off` adjust it, read left to right (`dev,cpu=600`). The flag wins over the
environment. Each limit is set soft and hard by `setrlimit`, as `ulimit`
does, and only ever lowered: under the suite's 6 GiB rail, `dev` stays at
6 GiB.

The CLI crate's lint goes from `forbid` to `deny` for the one function
that calls `getrlimit`/`setrlimit`, as `crates/cache` and `crates/linked`
do for theirs.

Moved to it: CLAUDE.md's rail, `scripts/fmt`, `scripts/linked`'s
`compile-x86` runs, `scripts/sentinel`'s library check.

## Left

- Scripts that cap a `heather` child from Python with `preexec_fn`
  (`scripts/showcase`, `scripts/perf`, `scripts/bench-probes`,
  `scripts/probe-whnf-sharing`) still do; nothing a user types carries it.
  `scripts/showcase --heather` can point at an older binary, which would
  not know the flag.
- `scripts/test`, `scripts/bench*` and `run-test-targets.mjs` cap `cargo`
  and test binaries, which are not `heather`: those stay `ulimit`.
- Limits are set in `main`, after the process has started; a memory limit
  below what it reserves before `main` (about a gibibyte) crashes rather
  than refuses. Setting them before the allocator's first arena would take
  re-running the binary (as `one_malloc_arena` in PR #649 does for
  `MALLOC_ARENA_MAX`); the two could share that one `exec`.
- A rail kill still reads as `signal 9` (CPU) or an abort (memory) with no
  message. Saying which rail was met needs a `SIGXCPU` handler (a soft CPU
  limit under the hard one) or a check in the allocator.
