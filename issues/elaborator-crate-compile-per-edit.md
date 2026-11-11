---
title: A one-line elaborator edit recompiles for two minutes
status: closed
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

## Log

- 2026-11-11: Done, by splitting the `Elaborator` type's methods across area views and by turning thin-local LTO off for the elaborator's incremental builds. Four-core cloud box, `cargo test --workspace --no-run` after one real edit:

  | edit | before | after |
  |---|---|---|
  | `resolve.rs`, the text of the `debug_assert!` message measured above | 123 s | 14 s |
  | one line added in `wf.rs` | | 24 s |
  | one line added in `checking.rs` | | 23 s |
  | one line added in `traits.rs` (`assemble_instance`) | | 22 s |
  | one line added to a method still on `Elaborator` (`lib.rs`) | | 31 s |
  | one line added in `crates/kernel/src/subst.rs` | 61 s | 42 s |

  Every test binary from an empty `target/debug` builds in 189 s. A cold showcase check (`calc_parser`, width one, the dev binary, five interleaved samples each) is 13.58 s before, 13.59 s with the views alone and 13.86 s with the pass off as well: +2.1%, inside the samples' spread (11.7 to 15.2 s). The fast lane's own total was not timed before and after; the check time is the evidence for "no slower".

  ### What the 114 s were (direction 4)

  `cargo rustc -p heather-elab-lib -- -Z time-passes` (stable takes it with `RUSTC_BOOTSTRAP=1`): front end about 4 s, `LLVM_passes` 18.5 s, `LLVM_thinlto` 42.6 s; 67 s for the crate alone, 114 s beside `heather-elab-unit`, which compiles the same sources at the same time.

  1. **One codegen unit held the elaborator.** rustc places a method with the module that defines its `Self` type, not with the file its `impl` block is in. All 979 `impl Elaborator` methods (51,209 lines in 53 files) were one unit: a 22.8 MB object of 1,294 functions, optimised again whole, on one core, after any edit. That is the 18.5 s.
  2. **Thin-local LTO redid the crate.** Once the units are optimised one by one, each inlines from the others, and after an edit that pass is redone for every unit that inlines from a changed one. 196 of the 256 units (128.8 of 132.7 MB) inlined from the `Elaborator` unit. That is the 42.6 s.
  3. **The crate's `Vec` code is one unit too.** Generic instances are grouped by the generic's own module: `Vec<T>` is one unit (11 MB of bitcode), the iterator adapters another (7.6 MB), drop glue a third (7 MB), and nearly every unit inlines from them. An edit that adds a line or changes a line's length moves the spans of the closures after it in its function, the `Vec` unit is generated again, and every unit that inlines from it is redone: 110 of 256 units and 46 to 48 s, even for an edit in `cutsat.rs`, whose own unit is 0.3 MB. An edit that keeps its line's length (other letters in a string) does not do this and costs 8 to 11 s. The first measurements of the split used such edits and read better than they were: **time an edit by adding a line.**

  ### What changed

  - **Area views** (direction 3, inside the crate). 733 `&self` and 99 `&mut self` methods moved from `impl Elaborator` onto 67 view types (`Wf<'e>(&'e Elaborator)`, `ClassesMut<'e>(&'e mut Elaborator)`), each defined in its area's module and dereferencing to the elaborator; another area calls `Wf(self).plan(..)`. `Elaborator`'s own unit is 1.6 MB. The views whose text was in `lib.rs` (8,161 lines: checking, inference, declarations, name lookup, the module pass, mismatch notes, refusals, application unification) moved to modules of their own, because a closure is placed with the module it is written in; `lib.rs` went from 11,945 lines to 3,758. The pattern and what differs from writing on `Elaborator` are in `crates/elab/src/lib.rs`'s module doc.
  - **`scripts/rustc-wrapper`**, wired as `build.rustc-workspace-wrapper` in `.cargo/config.toml`: `-C lto=off` for `heather_elab` and `heather_elab_unit` when the build is incremental. Cargo's `lto` is a profile-wide setting, and the kernel has to keep the pass.
  - **`scripts/codegen-units`** prints a build's units by size with the types and modules that fill each.

  ### Tried and set aside

  `cargo build -p heather-elab-lib` alone after an edit, and the showcase check with that dev binary. The first four rows are three samples each, not interleaved; the rest are five interleaved.

  | configuration | edit | check |
  |---|---|---|
  | master | 63 to 69 s | |
  | master, `lto = "off"` for the dev profile | 37 s | +23% |
  | master, elaborator at opt-level 2 (direction 1) | 62 to 66 s | +4% |
  | master, elaborator at opt-level 1 | 55 s | +18% |
  | views, LTO as it was | 46 to 56 s adding a line (8 to 27 s by area keeping its length, 48 s on `Elaborator`) | +0% |
  | views, `lto = "off"` for the dev profile | 13 to 18 s adding a line (5 to 7 s keeping its length) | +20% |
  | the same, kernel as one codegen unit | the same; a kernel edit 45 s, from 5.5 s | +3% |
  | the same, kernel as 4 or 16 units | | +15%, +21% |
  | views, LTO off for the elaborator only (landed) | 13 to 17 s adding a line (5 to 7 s keeping its length) | +2% |

  The kernel is the crate that needs the pass: its hot paths cross its modules.

  ### Left

  Direction 2 (the unit tests compile the sources a second time) is untouched, and so are the 9 to 10 s a real edit still pays for the `Vec` unit: [[elaborator-edit-recompiles-shared-vec-unit]]. The kernel's own edit is [[kernel-edit-rebuild-cost]].
