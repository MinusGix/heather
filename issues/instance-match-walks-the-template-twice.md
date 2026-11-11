---
title: Matching a type against a template walks the template twice and decodes each recovered code
status: open
labels: [elab,performance]
area: language
created: 2026-11-11
updated: 2026-11-11
---

Left over from `issues/template-instance-rebuilt-per-asking.md`, which made building an instance once per template and arguments. On a cold check of the x86 certificate of `examples/x86-native/levels.hthr` (callgrind, width one, 103,932 M instructions) the same area still holds:

- `instance_match_entry` walks the template against the subject twice (`Holes::ty`, 2,267 M) and decodes each recovered code (766 M).
- A hit in the instance table compares equal arguments that sit on different nodes (595 M). They would be the same nodes if `inlined_arguments` did not build a new code for every type argument (720 M of `code_of`). That function reads the registry, so keeping its answers needs the registry's invalidation rules (`lifetimes.rs`).

Neither shows on the showcase; both are costs of native certificates, where width-indexed types are instantiated at literals thousands of times.
