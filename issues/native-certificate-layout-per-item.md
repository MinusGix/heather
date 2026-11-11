---
title: Every emission statement of a certificate worked the program's layout out again
status: closed
labels: [performance,native,compiler]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

Found while counting where a leaf's emission goes ([[native-emission-membership-scans]]): a probe that took one `{p}_e_#` statement of `sort_tool`'s certificate apart piece by piece gave every piece a few hundred to a few thousand evaluator steps, except the layout, which each statement spells `{src}().layout(io_data_low(), {p}_homes())`.

## What it cost

`Source::layout` is not a literal. The word count is `main.word_bound()`, a walk of the whole program (through `Source::of`), and the two register pools are filters of the register lists by the homes (`Homes::leaf_pool`, `Homes::registers`). On `sort_tool`: the word count 48,874 steps, the leaf pool 9,840, the taken registers 2,746, 61,453 together. The kernel checks each declaration in a value arena of its own, so every statement that reads a word paid it again: 140 of the 260 emission statements paid about 55 thousand steps each, against a median statement of 67 thousand. This is where the kernel-only rows of the unfold profile came from (`Nat::max`, `Node::reads`, `Node::mentions`, `StructuredRegion::ids`).

The cost grows as the program times its statements, since the walk is of the whole program.

## Fix

`write-elf` states the layout once, as a literal `{p}_layout()`: the word count and the capacities as read on the fork (`{p}_sizes`), the pools worked out in Rust from the homes' spelling (`layout_literal`, elf.rs). One theorem holds it to the computed one (`{p}_layout_is`, by `refl`), and every statement names the literal. A literal that is wrong is a statement the kernel refuses.

## Measured

`scripts/bench-probes --heavy --filter native/elf-cold`, two samples a side in one hour, the before side in a worktree of master (c72ba7f4). Seconds are the minimum.

| case | before | after | evaluator steps before | after |
|---|---|---|---|---|
| `native/elf-cold-sort` | 33.17 s | 30.66 s | 57,619,549 | 49,034,907 |
| `native/elf-cold-tac` | 25.79 s | 24.22 s | 37,657,742 | 31,979,751 |
| `native/elf-cold-head-n` | 15.89 s | 14.96 s | 18,897,702 | 16,593,062 |
| `native/elf-cold-yes` | 4.99 s | 5.19 s | 1,203,272 | 1,214,908 |

`yes_tool` gains the one theorem's steps and its seconds are inside the spread.

## Not done

`Source::of` still computes `words` from `main`, so anything else that reads `{src}().words` walks the program. In the certificate those are a handful of declarations, not one per statement.
