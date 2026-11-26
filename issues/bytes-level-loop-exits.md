---
title: The bytes level's loop: a pass ends per arm in going on or leaving (no flag word)
status: open
labels: [native,x86,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The bytes level's `Loop` has one `next` for going on and for leaving, its outputs are the whole state, and the lowering tests an exit bit only where a comparison made it. A source loop is a function whose arms end in a `Jump` (go on, with the next values) or a `Ret` (leave, with the results), so translating one costs a flag word set on each path, a compare of the flag at the end of each pass, and the tail after the loop copied into every arm that leaves. The end-to-end slice measured it on `count_newlines` and `copy_window` (design note §25), and it is the same cost the comparison with the old pipeline showed on every loop row (§17.8: one more instruction per continuing pass, six to ten bytes per loop).

## What is wanted

A pass that ends, per arm, in going on with the next values or leaving with the outputs: the loop's body is a tree of branches whose leaves say which. Then a `Jump` is a leaf that goes on, a `Ret` inside the loop is a leaf that leaves, no flag word exists, and the lowering's tail is one conditional jump per leaving arm (forward) and one jump back per continuing arm.

## Constraints

- One loop form. The present one is the instance whose body has a single test at its end; it is restated as that instance or its programs are rewritten, not kept beside the new form.
- Fuel is spent at the back edge, as now (§17.7).
- The assembler model lands a `Jcc` only forward (`issues/asm-landing-both-ways.md`); the layout must not need a backward one.
- Statement and a test by evaluation first (§24): the form, its meaning, the lowering's layout, and the slice's two loops lowered by evaluation with their bytes compared, reported before the lowering's theorem is re-proved.

## When

After [[bytes-level-out-of-room]], which is in the same modules.

## Done when

`count_newlines`' and `copy_window`'s loops from the slice lower with no flag word, the loop rows of `scripts/bytes-level-compare` are no longer than the old pipeline's, and the lowering's theorem covers the form.
