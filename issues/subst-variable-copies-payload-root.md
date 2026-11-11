---
title: A substituted variable was a copy of its payload's root, per occurrence
status: closed
labels: [kernel,performance,substitution]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Local substitution answered a variable with a `Term` by value, and the traversal put it in a new node. So every occurrence of a substituted variable cost a copy of its payload's root, and the payload's own node, which the substitution was holding, was never the one used.

## What that cost

Read off a callgrind profile of a whole cold check of `docs/showcase/calc_parser.hthr` (width one), where `Type::apply_local` and `Term::apply_local` were 9.8% of the instructions:

- **A copy of the root per occurrence.** 2.76 M variable substitutions each cloned the payload's root (a count increment per child), compared the copy with `Term::Var(v)` through the syntactic-equality entry to see whether the substitution was the identity there, and dropped it or allocated a node for it.
- **The payload's identity was lost.** The copy is a fresh node: no bounds in its head yet, and no entry in any memo keyed by address (conversion's shortcuts and verdict memo, the typing memo, the closed-pair table). An argument substituted into a signature at five places was five nodes that the checker then compared as strangers.
- **A lift per occurrence under binders, closed or not.** Under binders the payload was lifted by `shift_local` on the value, which starts below the root, so a closed payload was a rebuilt root and a variable payload was a mapper built and dropped. 996 K lifts, 538 K of them past the lifted table's four inline entries and into a hash table.
- **A mapper of about 900 bytes built and dropped per call.** The lifted table held `Term`s by value (104 bytes an entry) and the shared-node memo's two tables were inline: four `memcpy`s, a `memset` and two drop glues, about 490 instructions for each of 1.33 M calls, most of which record nothing.

## What is built

In `crates/kernel/src/subst.rs`:

- `Mapper::local_var` returns `Option<Rc<Term>>`: `None` when the variable stays, and otherwise the node to use, as given. The traversal no longer asks the shared-node memo about a variable at all; one node per payload and depth is the mapper's to keep (`Lifted`).
- `Lifted::at`: under no binder the payload's own node; a variable payload is the shared leaf at the lifted index with no table entry; a payload that lifting does not change (its bounds say so, no walk) is its own node at every depth; anything else is lifted once per depth through the node-level traversal, which skips at the root.
- `SubstLocal` tests the identity on the payload (a variable that lifts to the index it replaces), not by comparing terms.
- `InstTop` makes its by-value payload a node once and lifts it the same way.
- `NodeMemo`'s tables are made at the first node recorded.

## What has to hold

- The node handed out is the payload lifted to the depth, exactly what the walk built before; only which allocation holds it differs. `tests/subst_laws.rs` holds the operations to their laws over generated terms, with every self-check on.
- A payload skipped by its bounds is the claim the skip check already verifies; the fast path is not taken while a skip is being derived again, since that walk consults no bounds.
- `a_substituted_variable_is_the_payloads_own_node` states the sharing on pointers (a copy is equal): closed and open payloads, under a binder and not, `inst_top`, a variable payload, and `t[id]` being `t`.

## Results

Instructions over the whole check: 44,310 M to 41,472 M (-6.4%). (Both totals include about 4,400 M of scalar SHA-256 that only callgrind's CPU pays: valgrind does not report the SHA extensions the cache's hasher uses on this box. Against what a real run executes the fall is nearer 7%.) `Type::apply_local` inclusive 3,487 M to 1,980 M, `Term::apply_local` 866 M to 550 M. Lifts 996 K to 78.5 K; hash-table inserts for them 538 K to 2 K.

Counters move, in the direction of more shared nodes: on the showcase conversion queries fall a little on many items (for example `ordered_field::class OrderedRing` 22,444 to 22,213) and evaluation steps on some (`tactic::reflexivity` 53,910 to 51,109). `subst_memo_hits` no longer counts a variable's second occurrence, and `local_subst_nodes` no longer counts the walks of payloads that are not walked.

## Log

- 2026-11-10: Seconds, `scripts/perf ab --mode cold` on the showcase, cloud box, quiet, the smaller-nodes tip against this one. Width one, seven interleaved samples: wall 9.53 to 10.42 s before, 9.38 to 10.25 s after, median -4.6%, the sets overlap, not a result; kernel gate median -3.7%, not a result. Eight workers, five samples: wall 8.64 to 8.84 s before, 8.17 to 8.82 s after, median -2.9%, not a result. Peak RSS no change. Counters over the run: eval_steps 4,878,540 to 4,801,134, eval_drives 7,065,515 to 7,019,764, conv_misses 127,116 to 127,089, conv_shortcut_hits 1,583,098 to 1,578,739, syntax_eq_memo_hits 607,145 to 632,283, typing_memo_hits 257,284 to 259,150, subst_memo_hits 1,189,197 to 1,156,284, local_subst_nodes 16,053,498 to 15,944,804; 31 columns identical. `scripts/test --pr` on the code: 3917 passed, 0 failed; kernel unit tests at the tip 173 passed; kernel unit and integration tests with every self-check on pass. Held to the instruction count (44,310 M to 41,472 M), which this box does not show as a separated wall time.
