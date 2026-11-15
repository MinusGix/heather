---
title: Recursion over an m-member mutual group is still about m^1.6 after the signature is named and the sum balanced
status: closed
labels: [elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-27
updated: 2026-10-27
---

Left by [[mutual-group-recursion-gate-cost]] once the signature was named
(`docs/inductives/iwf-named-signature-design.md` §4). Filed first as the comb: a
family's shape was a right-nested sum, so a structural recursion's step was
a case tree Θ(k) deep, its convoy motives named the label as an `inr` chain
that deep, and each arm evaluated the named index functions down the chain.
[[wide-inductive-balanced-sum]] (PR #214) balances every sum of eight or
more summands, mutual groups' member sums included, so that part is done.

What is left, measured on master with both (the `mutual_group` ring of
`crates/elab/benches/frontend/fixtures/intricate.rs` plus one `sizeᵢ` per
member and a `refl`; `heather check --timings`, release, width one, cloud
box, whole file):

| m | before both | named signature | both |
|---|---|---|---|
| 80 | — | ~1.6 s | 1.44 s (gate 0.93 s) |
| 160 | — | 6.1 s | 4.4 s (gate 3.2 s) |

About m^1.6 from 80 to 160 (queries ×3.1, kernel steps ×3.9).
`inductive/mutual-recursion` is 1.28 over 4..32, about 1.5 from 16 to 32.
Not attributed since the balancing: the step's arm count is Θ(m) and each
arm should now cost about log m, so a superlinear residue means something
per arm still grows with m.

Acceptance: an attribution (stack samples or counters at m = 80 and 160)
naming what still grows per arm, and either a fix that brings
`inductive/mutual-recursion` towards 1, or a recorded reason it cannot.

## Log

- 2026-10-27: Attributed and fixed (2026-10-27). Counters and a per-gate probe on the ring
  at m = 40, 80, 160 (release, width one, cloud box), then gdb stack samples
  at 160. The recursion's gate (`size0#rec`) was about m², and two things in it
  grew with m per arm:

  - **Every mention of the family lowered its shape and index type afresh.**
    `Elaborator::iwf_sig` builds both per mention (sums of one summand per
    constructor and per member), so no two occurrences shared a node below the
    root: each `D#iarity x` the kernel judged compared the shape at `x` with
    the definition's domain node by node, and conversions of two instances
    walked both. `share_iwf_part` now keeps the last shape and index type per
    family and hands back that allocation when the fresh one is equal
    (`share_registered_lowering`'s guard). Syntactic-equality visits for the
    group at m = 160: 19.1M → 2.7M.
  - **The member index type met itself in two spellings at every case node.**
    The motive's (and `#rec`'s) `#j` is spelled by the member sum's registered
    code, `El(D#members#tycode)`, while `D#iout` returns the inline sum; the
    step's case tree converted the two once per node, each under one more
    binder, so the cross-head memo (keyed on Γ) never hit, and each decoded
    the code and walked the sum: most of the gate's evaluation steps. The
    kernel now keeps a conversion between two sides that read nothing of Γ but
    its base (locally closed types, `El(u^δ)`/`U^δ` at the empty substitution
    out of Γ, sums of those) under a key without Γ (`ClosedSide`, typing.rs
    §The typing memo; sampled hits re-converted in debug builds).

  | m | before | after | gate before | gate after | steps before | steps after |
  |---|---|---|---|---|---|---|
  | 40 | 206 ms | 109 ms | 144 ms | 56 ms | 76,465 | 21,878 |
  | 80 | 677 ms | 369 ms | 485 ms | 178 ms | 289,569 | 68,386 |
  | 160 | 2,352 ms | 1,202 ms | 1,820 ms | 566 ms | 1,121,297 | 230,924 |

  `size0#rec`'s own gate at m = 80 → 160: 53 → 116 ms, about linear (was 306 →
  1,289 ms). `inductive/mutual-recursion` 1.16 over 4..32 (one run; 1.28
  recorded). What still grows is outside the recursion: every member's
  statement gate re-judges the Θ(m) signature with a fresh checker (about two
  thirds of the remaining gate at 160), elaboration lowers the shape at every
  mention, and global shifts walk the shape though nothing in it moves; filed
  as [[iwf-member-statement-signature-per-gate]]. Test:
  `a_ring_converts_its_index_type_once_per_gate` (steps 3.55× from 16 to 32
  members on master, under 3× now).
