---
title: A one-line elaborator edit recompiles for two minutes
status: open
labels: [performance,build,tooling]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

A one-line edit to the elaborator costs two minutes of compiling before any test can start, about as long as the fast lane's tests. Found while writing [[performance-overview-2026-11-11]]; [[fresh-container-compile-cost]] is the cold build's issue.

## Measured

`cargo test --workspace --no-run --timings` on a four-core cloud box, 2026-11-11, after changing the text of one `debug_assert!` message:

| edit | rebuild | where |
|---|---|---|
| `crates/elab/src/resolve.rs` | 123 s | `heather-elab-lib` 114 s; `heather-elab-unit` (the same sources for the unit tests) 86 s beside it; the other 139 units 35 s of work in about 8 s of wall |
| `crates/kernel/src/subst.rs` | 61 s | `heather-kernel-lib` 30 s as a library and 30 s as its unit tests; the kernel's integration tests 71 s of work; the elaborator crates 5 to 7 s |

`cargo build --release -p heather-cli` after an elaborator edit is 96 s. Rounds that changed inlined or generic kernel code paid 200 to 230 s in `scripts/test`'s compile step, because the elaborator crate then recompiles as well.

Linking is not the cost any more (91 test binaries link in seconds with mold). The cost is one crate: incremental compilation is on, and a one-line change still recompiles for 114 s at opt-level 3.

## Directions

1. Try `opt-level = 2` and `1` for `heather-elab-lib` and `heather-elab-unit` in the dev profile, and record the rebuild and the fast and `--pr` lanes' test time for each. The level was chosen when every test elaborated the library; the fast lane replays images now.
2. Compile the elaborator's sources once: the unit tests are a second full copy.
3. Split the crate along the lines `crates/elab/src/lifetimes.rs` already draws, so an edit recompiles a part.
4. Find what the 114 s are (`cargo rustc -- -Ztime-passes` on a nightly toolchain, or `-Zself-profile`): front end, MIR optimisation or LLVM.

## Done when

A one-line elaborator edit rebuilds the test binaries in under a minute, with the fast lane no slower in total.
