---
title: Free-variable bounds were a tenth of a cold check as side tables; kept in the node instead
status: closed
labels: [kernel,substitution,performance,representation]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Found by sampling whole cold runs of `docs/showcase/calc_parser.hthr`
(gate and elaborator together), after [[abstraction-walks-the-type-twice]]
and [[binder-types-weakened-per-use]] had taken the two largest callers
above it.

## What it cost

`bounds.rs` answers, per syntax node, which local variables the subtree
reads and whether a weakening tail shows in its scope, and for the global
namespace `1 +` its largest free global variable. Every local and global
traversal asks, to skip what it cannot change, and so do closure identity,
the closed-value memo and the typing memo's strengthened scopes.

The answers were in direct-mapped tables keyed by the node's address: one
pair a thread for the substitutions, a second for the typing memo, a third
for the global namespace, each entry under a weak reference and filled at
the node's second query ([[bounds-metadata-taxes-one-shot-checking]],
[[subst-visits-closed-subtrees]]). The file was near the leaf in a tenth of
all samples of the run, three fifths of that in recomputation walks and two
fifths in probes.

A bigger or more associative table was the cheap fix to try first, so the
recomputation was split by cause with a shadow set of evicted keys: of 3.4 M
walks of a term node, 0.56 M (a sixth) recomputed an answer a collision had
evicted while the node was alive; the rest were the first walk of a node
the table had never held. No table size changes that. What a table adds to
a first walk is the probe per child, the weak reference per entry, and the
miss in a 4 MiB table that the node is not in.

## What is built

The answer is in the node. `Rc` is now the kernel's own pointer (`rc.rs`):
`Arc` around the value and a head of three words, empty at `Rc::new`,
filled once per question by `bounds.rs`, emptied by `Rc::make_mut` and
`Rc::get_mut` before they hand the value out. The head is atomics, so a
node shared between gate workers is answered by whichever asks first and
read by the rest.

- `bounds.rs` loses the three tables, the weak keys, the two-stage markers
  and the second copy of every query for the typing memo. A question is a
  read of the head, and the first one walks what has no answer yet.
- The objection the tables answered was that a field on the node is an
  invariant of every construction site (DESIGN.md §Representation). No
  construction site touches the head: it is filled by the one function
  that defines it.
- Skips are decided at first sight, so which subtrees a traversal skips is
  a function of the term. `local_subst_nodes`, `shift_global_nodes`,
  `subst_memo_hits` and `syntax_eq_nodes` varied from run to run on one
  binary; they are now exact.
- Workspace-wide, `use std::sync::Arc as Rc;` becomes
  `use heather_kernel::rc::Rc;`. Unsized payloads (`[T]`, `str`, `dyn`) and
  the gate's stores are plain `Arc`. The five methods that took
  `self: &Rc<Self>` are inherent methods of `Rc<IWfSig>` and `Rc<MSig>`.

## Left open

- A `Term` is 104 bytes, so a node with its head is in the allocator's
  160-byte class where it was in the 128-byte one. Measured memory still
  fell, because the weak keys had pinned every dead node's block until its
  slot was reused. Two routes put the node back in the 128-byte class. A
  `Term` of 88 bytes: the widest variants are the annotated eliminators
  (`Case`, three levels and six children), which could keep their
  annotations behind one pointer as `IWfSig` does, at about 400 pattern
  sites. Or a head of one word: both bounds and a narrower `uses` mask
  packed with saturation, which changes what `eval/withheld.rs`'s
  classification sees past the mask's width and adds arithmetic to the
  trusted base. Neither is taken here.
- The head has room for more: a structural hash would serve the Merkle
  walks and `syntax_eq`'s pair memo the same way.

## Log

- 2026-11-10: Built and measured, on the cloud box at width one.

  `scripts/perf ab --mode cold`, `docs/showcase/calc_parser.hthr`, five
  interleaved samples, before = the stack with the tables, after = this:

  | | before | after | |
  |---|---|---|---|
  | wall | 17.13 / 17.99 / 16.27 / 16.37 / 16.98 s | 15.37 / 14.83 / 14.35 / 15.55 / 15.56 s | −9.5%, separate |
  | kernel gate | 4.58 / 4.82 / 4.33 / 4.37 / 4.48 s | 4.10 / 3.92 / 3.87 / 4.06 / 4.22 s | −9.3%, separate |
  | peak resident | 492 / 497 / 500 / 495 / 522 MB | 454 / 460 / 429 / 431 / 426 MB | −13.1%, separate |

  41 count columns are identical across both binaries and every sample,
  conversion's among them. The four that varied from run to run before are
  one number now: `local_subst_nodes` 17.01 to 17.03 M before, 16,053,974
  after; `shift_global_nodes` 230,000 to 354,000 before, 55,361 after;
  `subst_memo_hits` and `syntax_eq_nodes` move by under a hundred.

  Whole-run instructions (callgrind): 52,773 M to 51,332 M (−2.7%), and
  `bounds.rs`'s own from 2,730 M to 800 M. The seconds fall three times as
  far as the instructions do because what the tables cost was mostly misses.

  `scripts/bench`, both trees twice, interleaved, same box: of 102 rows 39
  are faster with the two runs' ranges apart and 4 slower (`subst/shift-local`
  at two sizes, 1.08×; `nat/step-once` at two sizes, 1.04 to 1.08×, a step of
  0.3 µs); geometric mean 0.94×. `code/check-identity-recursor`, the one-shot
  check the two-stage fill was tuned for ([[bounds-metadata-taxes-one-shot-checking]]),
  is 0.74 to 0.83×. No fitted slope moved outside its two runs' spread.

  Peak memory fell although a term node grew from the 128-byte class to the
  160-byte one: each table entry's weak key held a dead node's block until
  the slot was reused, six tables a thread.
- 2026-11-10: The head is two words (2026-11-10, with [[kernel-level-eight-bytes]]). The flags had a byte and seven bytes of padding to themselves; they are now the top four bits of the word that holds the mask of used indices, which covers indices below 60 instead of 64 (`rc::USES_BITS`). The mask is the one part of an answer that is about cost: its only reader is `bounds::ignores_innermost`, asked about index 0 by the evaluator's probe, and "a wrong answer costs time, never a verdict". The bound and the global bound keep all 32 bits, so no skip decision changed. The flag and the mask are published by one `fetch_or`, which is one write fewer than before.

  With `Arc`'s two counts a node is four words over its value: a term 112 bytes, a type 80. What that buys is in [[global-allocator]]'s log, since it only shows under an allocator that serves those sizes from their own classes.
