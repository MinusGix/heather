---
title: A one-line kernel edit rebuilds the test binaries for forty seconds
status: open
labels: [performance,build,tooling,kernel]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

A one-line kernel edit rebuilds the test binaries in 42 s (`crates/kernel/src/subst.rs`, one comment line added inside a function, `cargo test --workspace --no-run`, four-core cloud box, 2026-11-11; 61 s when [[performance-overview-2026-11-11]] measured it). [[elaborator-crate-compile-per-edit]] took the elaborator's edit from 123 s to 14 to 31 s and left the kernel as it was, because what fixed the elaborator does not carry over.

## What is known

- The kernel is compiled twice per edit, as a library and as its unit tests, at opt-level 3; the overview measured 30 s for each.
- `cargo build -p heather-elab-lib` after an edit in `conv.rs` that keeps the line's length is 5.5 s, so the kernel's own units are not the cost. Whether an edit that adds a line is much dearer, as it was in the elaborator (the shared unit of generic code is regenerated and thin-local LTO redoes every unit that inlines from it), has not been measured for the kernel.
- The kernel cannot simply lose the pass: with `lto = "off"` for the whole dev profile a cold showcase check is 20% slower, and 3% slower when only the elaborator loses it, so about 17 points are the kernel's cross-module inlining. Compiled as one codegen unit the kernel keeps its speed without the pass, and then every kernel edit is 45 s; as 4 or 16 units it is 15% and 21% slower.
- `scripts/codegen-units --crate heather_kernel`: `rec` 4.4 MB in 31 functions, `subst` 3.7 MB, drop glue 1.7 MB.

## Directions

1. Measure first: `cargo rustc -p heather-kernel-lib -- -Z time-passes` (`RUSTC_BOOTSTRAP=1` on stable) after an edit that adds a line, and count the objects rewritten, as `scripts/codegen-units` lists them.
2. If the pass's fan-out is the cost: `#[inline]` on the small functions the hot paths call across modules, then the pass off for the kernel as well (`scripts/rustc-wrapper`), measured against the showcase check.
3. The unit tests' second compile: kernel unit tests at a lower opt-level, or fewer of them in the library crate.

## Done when

A one-line kernel edit rebuilds the test binaries in under twenty seconds with the showcase check no slower, or the measurement shows why not.
