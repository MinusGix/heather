---
title: Abstraction weakened the whole type, then walked it again without skipping
status: closed
labels: [kernel,substitution,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Found by sampling whole cold runs of `docs/showcase/calc_parser.hthr` (gdb
stacks, gate and elaborator together): the kernel gate is about a third of
such a run, and kernel code called from the elaborator is a larger share
than the gate. The largest single caller was `Type::abstract_local` and
`abstract_pats`, from the elaborator's motive construction (`matching`).

## What it did

`t.abstract_local(p)` finds the occurrences of `p` in `t` and replaces them
by a fresh variable 0. It was two traversals: `t.shift_local(1)` to make
room, building a second copy of every open node, then the search over the
copy. The search asked no bounds question, so it also walked every closed
subtree of the copy, which cannot hold an occurrence of an open pattern and
which the weakening had just shared.

## What it does now

One traversal (`subst.rs` `AbstractLocal`). The mapper weakens as it walks
(`local_var` and `tail` do what `ShiftLocal` by one does), the patterns are
weakened once up front instead of the subject, and a subtree that reads no
variable at or above the walk's depth is returned as it is
(`bounds::skip_type`/`skip_term`), provided every pattern is open: a closed
pattern can occur in a closed subtree, so then nothing is skipped.

`tests/subst_laws.rs` holds it to the old meaning:
`abstraction_inverts_substitution` now also asks that the result has no
occurrence left (maximality), and `abstraction_shares_what_it_cannot_change`
asks that a closed subtree comes back the same node and that a closed
pattern is still found inside one.

## Log

- 2026-11-10: Built. `scripts/perf ab`, cold showcase, cloud box, width one:
  the elaborator's `matching` phase 0.75 s to 0.12 s, every sample separate;
  `subst_memo_hits` 3.36 M to 1.19 M. Conversion's counters are identical.
  Measured together with [[binder-types-weakened-per-use]]: wall median
  17.16 s to 16.30 s (−5.0%).
