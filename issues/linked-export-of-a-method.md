---
title: An exported function cannot be a method: the table and compile-x86 take one identifier for name, label, file and Rust name
status: closed
labels: [native,exports,tooling]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

An exported function cannot be a method. `compile-x86` and `crates/linked/generated/EXPORTS.tsv` take one ASCII identifier that is at once the Heather function's name, the assembly label, the generated file's stem and the Rust declaration's name, so `List::sha256_update` cannot be a row (2026-11-12).

What it costs today: SHA-256's storing functions are `mut self` methods on the span ([[mut-self-tail-branch-receiver]]), and the four that are exported are not. Each exported entry point is a plain function that opens `let mut ctx = ctx;` and ends `Mutated(ctx, value)` (`sha256_compress`, `sha256_init`, `sha256_update`, `sha256_finish` in `lib/native/crypto/`), which is the one place the modules still spell the threading by hand. [[sha256-context-type]]'s last stage (a `runtime fn` whose receiver is the laid-out record) needs it outright: `Sha256::update` is a method or it is nothing.

## What it takes

- A row names the function as Heather does (`List::sha256_update`, later `Sha256::update`) and the symbol separately. Either a column for the symbol, or a rule that derives it (`Sha256::update` as `sha256_update`), with the table refusing two rows that derive one symbol. The symbol stays the label, the file stem and the Rust name.
- `compile-x86` takes the same spelling on its command line.
- `scripts/linked` and `generated/exports.rs` follow; `tests/linked_exports.rs` holds them.
- A `mut self` receiver that is a span is the row's `name: span mut` parameter; nothing else about the calling convention changes.

## Done when

A `mut self` method is a row of `EXPORTS.tsv` under a symbol, linked and called from Rust with a test against a reference, and a control row whose symbol collides is refused by name. The SHA-256 entry points moving to methods is a follow-up in [[sha256-context-type]], not this issue.

## Log

- 2026-11-12: Built on PR #551's branch: a row names the function by its path and is exported under a symbol (derived, `Type::method` as `type_method` in snake case, or written `sym = Type::method`); compile-x86 --symbol; heather linked-exports --rows; two rows with one symbol refused by name. First row: List::raise_letters (native_tool_spans) as list_raise_letters, held to raise_span's reference in crates/linked/tests/spans.rs. docs/native/native-library-exports-design.md §6.4.
