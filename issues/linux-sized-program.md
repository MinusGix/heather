---
title: ITree::sized of a Program's trees is a Program
status: open
labels: [itree,semantics,proofs]
area: heather-in-heather
milestone: [hih-pl-spec]
created: 2026-10-21
updated: 2026-10-21
---

`ITree::sized(max, t)` (`lib/std/os/linux/linux_trees.hthr`) turns a size-free spec tree
into one that asks for `max` bytes at every read, and
`ITree::implements_sized` proves it implements the spec, tree by tree. A
`Program` also carries growth (`Below` from one fuel to the next), so
`Program::Implements` for `sized` needs translate to preserve `Below`
(`ITree::translate` in `lib/std/itree/itree.hthr`). The lemma is general: any event
map preserves `Below` and `Same`. It belongs in `itree_trace`, beside
translate's other laws.

## What it assumes from elsewhere

- **[[native-linux-spec]]** owns `Implements` and `sized`. Assumed here: only
  that `sized` is `translate` over `EventMap::linux_sized`.
