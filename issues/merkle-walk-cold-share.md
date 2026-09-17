---
title: The merkle walk is a sixth of the showcase's wait and all of some cheap declarations: attribute and memoize
status: open
labels: [tooling,caching,performance,measurement]
created: 2026-09-17
updated: 2026-09-17
---

Found by the first `scripts/perf snapshot` ([[perf-dashboard]], 2026-09-17,
desktop, width one): the merkle walk — the content-addressing walk over each
declaration's kernel binding (`crates/cache/src/merkle.rs::interface_hash`
and `check_key`) — is **6% of a cold check summed over the corpus**, and on
the showcase 3.1 s of 53.6 s cold and 16% of the width-8 wait, where every
other elaborator phase has shrunk under it. The walk is pure hashing: it
neither elaborates nor checks anything, and it runs on the cold path too,
where nothing can be reused.

Per declaration on `docs/showcase/calc_parser.hthr` (cold, from the
snapshot's raw table):

| declaration | merkle ms | of its total | decls_gated |
|---|---|---|---|
| `parser_primitives::complete_post` | 513 | 5% | 2 |
| `calc_parser::close_body` | 300 | 10% | 2 |
| `calc_parser::open_body` | 197 | 52% | 2 |
| `calc_parser::number_grammar` | 184 | 8% | 2 |
| `calc_parser::factor_body` | 169 | 12% | 2 |
| `calc_parser::plus_selected` | 163 | 96% | 2 |
| `calc_parser::Grammar` | 128 | 12% | 34 |
| `calc_parser::expr_body` | 105 | 8% | 2 |
| `calc_parser::checked_expr` | 93 | 7% | 30 |
| `omega::cutsat_left_cut` | 77 | 5% | 2 |

Two shapes in that table:

- On the heavy proofs (`complete_post`, `close_body`) the walk is 5–10% of
  the item: a tax proportional to the emitted term, the same size the
  normal-form emission issue prices ([[elab-emits-normal-form-of-matched-type-argument]]).
- On `plus_selected` (96%) and `open_body` (52%) the walk **is** the item:
  declarations the kernel finishes in milliseconds whose statement or body
  is large enough to spend 160–200 ms hashing. The walker's own rule is
  "a declaration's content exactly once" (`check_key`'s doc), so these are
  declarations whose *content* is that large — an emitted spelling the
  kernel can walk cheaply (sharing, shortcuts) and the hasher cannot (it
  sees a tree).

## Questions the round should answer, in order

1. **Is the hasher walking shared structure as a tree?** Elaborated terms
   share subtrees aggressively; a walk that revisits an `Rc` subtree per
   occurrence pays the *tree* size while the kernel pays the *graph* size.
   [[warm-path-rewalks-unchanged-declarations]] already names a per-`Rc`
   in-run memo as its first candidate for the warm path; on the cold path the
   same memo would collapse `plus_selected`'s 163 ms to its graph size. Count
   nodes visited against distinct `Rc` addresses on `plus_selected` before
   anything else — if the ratio is large the fix is one table and the
   determinism rule (pointer identity changes how fast, never what).
2. **Where does `plus_selected`'s content come from?** If its statement is
   the normal form of something, the emission issue owns the size and the
   walk is only the messenger; the memo still pays either way.
3. **Is the walk on the critical path at width > 1?** `check_key` runs
   before the gate is deferred; if it runs on the elaborator's thread it
   serializes ahead of the workers, which is how 6% at width one becomes 16%
   at width 8.

## What it assumes from elsewhere

- **[[warm-path-rewalks-unchanged-declarations]]** owns not walking unchanged
  declarations on a warm run. Assumed here: only that its memo candidate is
  also the cold path's, so one round can take both.
- **[[parallel-checking-and-caching]]** owns the cache identity design; the
  walker's injectivity and exhaustive-match discipline stay as they are.
- **[[elab-emits-normal-form-of-matched-type-argument]]** owns emitted size.
- **[[perf-dashboard]]** is where the number came from and where a fix is
  re-measured (`scripts/perf snapshot --corpus quick --only calc_parser`).
