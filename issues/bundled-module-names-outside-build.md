---
title: Programs that import bundled module names can't be checked outside build-x86
status: open
labels: [cli, loader, native, ergonomics]
created: 2026-09-29
updated: 2026-09-29
---

The native builder bundles its proof library under harness names that are not
file stems: `bitvec_omega` is `lib/std/bitvec/omega.hthr`, `bitvec_nat` is
`lib/std/bitvec/nat.hthr`, and the x86 modules have their own aliases. Since
2026-09-29 `build-x86` lets a program import them
([[load-providing-swallows-resolve-errors]] has the mechanism), but `heather
check examples/x86-native/wc.hthr` still fails with "cannot find module
`bitvec_omega`", so the program's proofs can only be iterated through a probe
directory of renamed copies or a whole build.

Two spellings of one module is the root: either give those modules their
harness names as files (or `-L` aliases the loader understands), or teach
`check` the same bundle table. Related: the memory note about probe
directories is the workaround in use.
