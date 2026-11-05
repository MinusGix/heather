---
title: write-elf: lower, allocate and check sources with procedures a part at a time
status: open
labels: [native,compiler]
area: heather-in-heather
milestone: [nh-procedures]
created: 2026-11-01
updated: 2026-11-01
---

Residue of [[native-compiled-procedures]] (closed 2026-11-01): what `heather write-elf` does for sources with procedures that it does more cheaply for sources without them.

## Scope

- **A builder tool with procedures is lowered whole.** `write-elf` reads such a tool's `source().spelled()` as one literal and states `{tool}().source() = {p}_lowered()` by one `refl` (crates/cli/src/native/elf.rs, `in_parts`). The part-at-a-time lowering (`lib/native/native_build_parts.hthr`, crates/cli/src/native/parts.rs) walks `main` only: `Tool::source_of` takes `t.opened(0).procedures = []`. grep -F fits in one declaration's fuel; a tool whose procedures' bodies are a few times larger will not. Extend the part-wise statements to each procedure's body (`Proc::lowered`, the results zeroed before the body) and drop the premise.
- **The Rust allocator mirror skips procedures.** `allocator::homes_spelled` returns `None` for a source spelled `[2]`, so its homes come from `Source::homes` evaluated on the fork, which keeps every value it forces until the read returns (the reason the mirror exists). Mirror `List::bodies_needs`, `bodies_graph`, `bodies_weights` and the fallback's `bodies_check` (lib/native/native_alloc.hthr), keeping `HEATHER_ELF_ALLOCATOR=both` as the agreement check.
- **The procedures' `fits` is one `refl` each** (`{p}_pf_{i}`, crates/cli/src/native/emission.rs): its `checked` pass over the whole body is not stated a part at a time as `main`'s is (`{p}_ck_`).

## Done when

A builder tool with procedures goes through the part-wise lowering, the Rust allocator gives a source with procedures the fork's homes (checked by `HEATHER_ELF_ALLOCATOR=both` in a test), and a procedure's check is stated over its body's parts.

## Log

- 2026-11-05: gardener: cites a file it shares with [[kernel-failed-conversion-cost]] (`crates/cli/src/native/elf.rs`); [[native-allocator-cost]] (`lib/native/native_alloc.hthr`); [[native-certificate-fork-byte-reads]] (`crates/cli/src/native/emission.rs`); [[self-hosted-compiler]] (`crates/cli/src/native/elf.rs`).
