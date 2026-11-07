---
title: Comparing two long VecItems nodes by value is quadratic in their length
status: open
labels: [kernel, conversion, literals, performance]
area: kernel
created: 2026-11-07
updated: 2026-11-07
---

Since docs/deep-term-walks-design.md §3.4 conversion
compares two long vectors component by component at constant native depth,
so two separately built `Term::VecItems` nodes of any length compare. The
time is quadratic: each step unfolds the node one element
(`vec_items_unfold`) into a pair whose tail is a *fresh* `VecItems` node at
`from + 1`, and the value machine's closed-term memo key
(`value.rs`, `closed_ident` → `bounds::term_local_use`) computes that
node's bounds, which loop over its whole live window (`bounds.rs`,
`compute_term`'s `VecItems` arm). The window cache misses every time, since
every tail is a new node.

## Reproduction

`a_node_longer_than_any_chain_the_stack_holds_checks`
(`crates/kernel/tests/bitvec_values.rs`) compares two 20,000-element nodes
by value; at 200,000 it does not finish in five minutes, with gdb samples
all in `compute_term`'s `VecItems` loop under `memo_closed`.

## Direction

The window's bounds are a suffix join of the items' summaries. Options, each
exact:

- a summary per items array (keyed by the `Rc<[…]>`'s address, kept alive
  by it) holding suffix joins at a stride, so a window's summary is one
  lookup plus at most a stride of joins;
- carrying the summary of the from-0 window on the node when every item is
  closed (the literal case): every window of a closed array is closed.

Measure with `scripts/perf ab`; the literal case (all items closed) is the
one the elaborator emits.
