---
title: Substitution builds every unchanged node and drops it: the refcount pair the Arc tax lands on
status: open
labels: [kernel,performance,representation,substitution]
area: kernel
created: 2026-09-11
updated: 2026-09-11
---

`subst.rs`'s `sub_ty`/`sub_tm` always call `map_type`/`map_term` to build a replacement node, then — if the mapper reported no change — `drop` it and return `Rc::clone(orig)` (`shared_ty`/`shared_tm`). The built node allocates nothing (its children are `Rc` clones), but it costs one refcount increment per child on the way up and one decrement per child on the drop.

That clone/drop pair is where the `Arc` tax measured in [[kernel-arena-terms-frozen-prefix]] lands: `nat/step-once` 128 -> 163 ns (1.28x), `nat/step-into-closed-body` 1.24x, `nat/add-normalize` and `nat/mul-normalize` 1.20x, against 1.02-1.06x everywhere the work is conversion rather than substitution. Under `Rc` the pair is two non-atomic increments; under `Arc` it is two atomic RMWs, and these four families are the ones that do nothing else.

The `skip_ty`/`skip_tm` bounds hooks already remove the pair for a subtree a *local* operation provably cannot touch ([[subst-visits-closed-subtrees]]). What remains is the node that is visited, is changed nowhere below, and is rebuilt anyway — and every node on the spine above a change, where the rebuild is real but the children that did not move are still cloned-and-dropped through the temporary.

## The shape of a fix

Have the traversal return "unchanged" rather than a rebuilt node: `sub_tm` returning `Option<Rc<Term>>` (or a two-case enum) with `None` meaning "reuse the original", so a node is constructed only when at least one child actually moved. That is a rewrite of every arm of `map_type`/`map_term`/`map_motives`/`map_branches` — mechanical, but wide, and in the trusted base with the 300-seed law suite and the `shared_*` debug assertions behind it. It wants its own round with `scripts/bench --check` on the four families as the acceptance number, not a corner of someone else's.

Raised out of [[parallel-kernel-gate]] (2026-09-11), whose clone/drop audit found this and deliberately did not attempt it: the audit's premise was that there were gratuitous pairs to delete, and there is exactly one, structural.

## What it assumes from elsewhere

- **[[kernel-arena-terms-frozen-prefix]]** owns the representation answer, under which this cost disappears entirely (cloning a term becomes copying a `u32`). Assumed here: only that the arena is not imminent, so a representation-preserving fix is still worth its round. If the arena lands first, close this.
