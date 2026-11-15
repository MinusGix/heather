---
title: Programs that import bundled module names can't be checked outside build-x86
status: closed
labels: [cli, loader, native, ergonomics]
created: 2026-09-29
updated: 2026-09-29
---

The native builder bundles its proof library under harness names that are not
file stems: `bitvec_omega` was `omega.hthr` in `lib/std/bitvec/`, `bitvec_nat` was
`nat.hthr` there, and the x86 modules have their own aliases. Since
2026-09-29 `build-x86` lets a program import them
([[load-providing-swallows-resolve-errors]] has the mechanism), but `heather
check examples/x86-native/wc.hthr` still fails with "cannot find module
`bitvec_omega`", so the program's proofs can only be iterated through a probe
directory of renamed copies or a whole build.

Two spellings of one module is the root: either give those modules their
harness names as files (or `-L` aliases the loader understands), or teach
`check` the same bundle table. Related: the memory note about probe
directories is the workaround in use.

## Log

- 2026-09-29: Fixed by giving each module its name as a file, not by teaching `check` the
  bundle table. The eighteen files whose stems weren't their module names were
  renamed: `lib/std/bitvec/{nat,omega}.hthr` → `bitvec_nat.hthr`,
  `bitvec_omega.hthr`; `lib/std/arch/x86_64/model.hthr` → `x86_64.hthr`, and every
  other file there took the `x86_64_` prefix it already had as a module name
  (the `lib/std/parser/parser_*.hthr` convention). The loader now looks below
  each search directory after a miss in the directories themselves
  (docs/language/modules-design.md §3.2; before, only a directory *target* got that
  tier), so no client names `lib/std/arch/x86_64` or `lib/std/bitvec`.
  `heather check -L lib/std -L lib examples/x86-native/wc.hthr` checks, as do
  `lib/std/parser/parser.hthr`, the x86 modules in place and the whole native library
  stack (`lib/elf64_read_fields.hthr`). The perf corpus row for the x86 model is
  now keyed `lib/std/arch/x86_64/x86_64.hthr`.
- 2026-09-29: The lower tier skips dot-directories, and the editor server no longer searches
  the workspace root (lib/std, lib and the file's directory, as the CLI does):
  below the root, `target/` and `probes/` hold copies of `bitvec_omega` and
  friends, each a second hit. A walk of the whole repository is a fraction of a
  second once directories are deduplicated through one set of canonical paths.
