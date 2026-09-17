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

## Log

- 2026-09-17: 2026-09-17: The three questions, answered in order on the showcase (desktop,
  release, a temporary visit/address/byte counter in the walker, removed again).

  **1. Tree or graph?** Over the whole cold check the walker visited 51.8 M
  nodes against 24.7 M distinct addresses — a ratio of **2.1**, at most 3.8 on
  any one walk (the cutsat lemmas; `complete_post`'s check walk is 1.7). So a
  per-`Rc` memo is worth at most 2× and is *not* where `plus_selected`'s 96%
  comes from. It fed **445 MB** through SHA-256, which runs at 318 MB/s here
  (measured on a flat buffer), so the hashing itself was ~1.4 s of the 3.1 s
  and the walk-and-encode the rest.

  **2. Where `plus_selected`'s content comes from.** Not answered by the
  counter and no longer the point: its content is large because its emitted
  statement is, which [[elab-emits-normal-form-of-matched-type-argument]]
  owns; the walk was paying it *twice*, which is the finding below.

  **3. Why 6% at width one became 16% at width eight.** The labelled probe
  showed every declaration's interface walked **twice** at width one and its
  whole identity computed twice at width eight. Two memo failures in
  `crates/cache/src/lib.rs`, both in the "hash once for the `admits`/`accepted`
  pair" discipline the code already claimed:

  - inline gate: `accepted`'s `sync` cleared `pending` unconditionally, so the
    interface hash it was holding for the binding about to land was thrown
    away and the next item's `sync` re-walked the binding;
  - deferred gate: `accepted` runs at the join, with the Ψ *snapshot* the item
    was queued under, long after `last` (a one-entry memo keyed on Ψ length)
    had moved on — so every item was fully re-hashed at the join, and the
    first `accepted` of a module, seeing a prefix longer than its snapshot,
    cleared and rebuilt the whole prefix.

  Fix: the one-entry memo becomes an exact map of **open questions**, keyed
  by Ψ length then name and opacity: opened by `admits`, closed by the
  `admits` hit or the `accepted` that answers it, and killed by a new
  `KernelGate::abandon(psi)` hook the elaborator calls on every declaration
  failure — needed because the module loop keeps going after a refused
  declaration and the next one lands at the same Ψ length (a same-named one
  with different content would otherwise inherit the dead answer). As a belt,
  a second Ψ-landing question at one length kills the first. `Counts.hashed`
  counts full renders; two tests pin one render per gated declaration at
  widths 1 and 4, and the abandon/belt semantics at the gate interface.

  Measured (run rows of the snapshot's raw tables, same tree otherwise):

  | showcase | cache_hashes | merkle_walk |
  | - | - | - |
  | wait, width 8, before | 2122 | 5.86 s (16.8% of 34.9 s) |
  | wait, width 8, after | 1061 | 2.36 s (6.9% of 33.9 s) |
  | cold, width 1, before | 1061 | 3.02 s |
  | cold, width 1, after | 1061 | 2.18 s |

  omega is unmoved (0.4 s either way: its interfaces are small, its cost is
  the check walks). Residue noted while here: `cache_hash_ns` reads 0 on
  every row because `merkle_walk` nests inside it and timers are exclusive —
  the column means "identity time that is not the walk" and is ~0.
- 2026-09-17: 2026-09-17: The second lever, measured and **not taken**: the hash's rate.
  After the open-question fix the showcase's cold walk feeds ~300 MB through
  the first-party SHA-256, which runs at **318 MB/s** on this box (a flat
  512 MB buffer through `Sha256::update`), so ~0.95 s of the remaining
  2.18 s is the compression function itself, with the walk-and-encode the
  other ~1.2 s. The CPU's SHA extensions (`sha_ni`; the desktop and the
  furnace's EPYC both have them) run the same function at roughly five times
  that rate, and a first-party `std::arch` path — Intel's reference schedule,
  ~90 lines, selected per hasher by `is_x86_feature_detected!`, with a
  `Sha256::scalar()` constructor so the existing oracle tests check both
  paths against each other on one machine — was written and refused by the
  build: the workspace forbids `unsafe_code` and the intrinsic call needs one
  `unsafe` block ([[dependency-policy]] records the forbid as a decision that
  binds our code and not a dependency's). Two routes, both a policy call and
  so neither taken here:

  1. **One `#[allow(unsafe_code)]` on the dispatch**, the intrinsics verified
     by the same NIST vectors and the independent oracle the scalar rounds are
     verified by. The trust argument for the first-party hash (a frozen spec
     with a checkable criterion) applies to the intrinsic path unchanged — the
     rounds are the CPU's, the schedule is the paper's, the test is the same.
  2. **`sha2` as a runtime dependency of the cache crate.** It is already in
     the tree as the test oracle, ships the extensions path, and the forbid
     does not bind it; the price is [[dependency-policy]]'s audit for a crate
     that is above the kernel but carries the rung-1 trust story.

  Worth ~0.8 s of a 55 s cold showcase check and ~0.8 s of its 34 s wait —
  real but not large; the walk's remaining half is the encode over 25 M
  distinct nodes visited 1.7–2.1× over, whose 2× ceiling is the per-`Rc` memo
  [[warm-path-rewalks-unchanged-declarations]] names.
