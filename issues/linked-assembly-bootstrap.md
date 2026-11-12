---
title: The heather binary links the assembly it generates: a broken generated file cannot be regenerated
status: open
labels: [native,tooling,dx]
area: heather-in-heather
milestone: [self-lexer]
created: 2026-11-12
updated: 2026-11-12
---

Since `HEATHER_LEXER=linked` (PR #551) the `heather` binary links `crates/linked` on x86-64 Linux, and `crates/linked/generated/*.s` is written by that binary (`scripts/linked`). A generated file that does not define the symbols `crates/linked/src` declares therefore stops the binary from linking, and the binary is what would regenerate it.

Met once (2026-11-12): merging master into a branch that had added entries to `scan_token.s` (`scan_accept`, `scan_begin`), the conflict was resolved to master's file, and every build of `heather-cli` failed with `mold: error: undefined symbol: scan_token`. Nothing in the message says the fix is a checkout.

The way out today: restore a complete generated file from either side (`git checkout HEAD -- crates/linked/generated/<file>.s`, or `MERGE_HEAD`), whichever defines every symbol the current `src/` declares; build; run `scripts/linked`, which rewrites it for the merged sources. A stale but complete file is harmless for this: the scanner's answers are only used where the Rust lexer agrees, and `scripts/linked` does not lex through the linked scanner unless `HEATHER_LEXER=linked` is set.

Options, cheapest first:

1. **Say it where it is met.** A line in `CLAUDE.md`'s `crates/linked` bullet, and `scripts/linked` printing the recovery when its own `cargo build` fails at link with an undefined `scan_*`/`sha*` symbol.
2. **A build without the linked code.** A `--no-default-features` build (or `HEATHER_NO_LINKED=1` read by a build script) of `heather-cli` that leaves `heather-linked` out, which `scripts/linked` uses to regenerate. The switch was built without a feature on purpose (one binary, chosen at run time), so this would be a bootstrap-only configuration and needs its own test that it still builds.
3. **Weak symbols**: the generated symbols declared weak with a Rust fallback that refuses. More machinery than the problem.

Recommended: 1 now, 2 when a second linked component the binary itself uses arrives (the SHA-256 in the cache, if Minus takes that step).

## Done when

A merge conflict in `crates/linked/generated/` has a written recovery that the failing command points at, or the binary that regenerates the files does not need them.
