---
title: Structural recursion over an m-member mutual group costs about m^2.8 in the gate, and runs out of fuel at eight members
status: open
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-26
updated: 2026-10-26
---

Found by the intricate-inductive bench families
([[intricate-inductive-bench-families]], `inductive/mutual-recursion`). A
ring of `m` sorts, each `inductive Mᵢ { Lᵢ, Nᵢ(a: Mᵢ₊₁, b: Mᵢ) }`, one
`sizeᵢ` per member, and one theorem `size0(N0(a, b)) = add(size1(a),
size0(b))` by `refl`. Declaring the group is cheap and about linear
(`inductive/mutual-declaration`). Recursing over it is not.

`heather check --timings`, release, width one, cloud box:

| m | `size0` (the group) total / gate | queries | the one-step `refl` |
|---|---|---|---|
| 2 | — | — | — (0.32 s whole file) |
| 4 | 1,475 / 1,427 ms | 1,056,100 | 479 ms |
| 6 | 5,016 / 4,938 ms | 4,538,604 | 1,330 ms |
| 7 | 8,870 / 8,715 ms | 7,996,985 | 2,190 ms |
| 8 | 13,629 / 13,432 ms | 13,124,780 | **kernel `OutOfFuel`** |

97% kernel gate at every size. **Control:** the same twelve constructors as
*one* recursive inductive (`T { L₀…L₅, N₀(a: T, b: T)…N₅ }`, the same `size`
and the same `refl`) is 5.3 ms in total, against 6.4 s for the six-member
group: the cost is the mutual encoding, not the constructor count.

The gate's samples sit in `tm_check_inner`/`tm_infer_memo` recursion over
`iwf_sig_wf`, and conversion `tm_w → tm_nf_sum → tm_ne_case` nested through
the member sum (gdb, eight samples at m = 8). Unattributed past that.
Plausible shape: the group's `f#mot` is a `match` on the member index whose
every branch is a Π over that member's index, and the generated `elim_IWf`
instantiates it per constructor of every member, so each of Θ(m) arms
carries a Θ(m) motive whose conversions case-split over the Θ(m) member sum.

Why it matters now: the heather-coq port, the customer of
[[mutual-inductive-declarations]], wants a group of four syntax sorts and one
of seven judgments; seven is 9 s of gate for one `size`, and eight is past the
fuel limit for a one-step unfolding.

Acceptance: `inductive/mutual-recursion` drops towards 1 in the members,
re-recorded from below, and the m = 8 `refl` checks.

## What it assumes from elsewhere

- **[[mutual-inductive-declarations]]** owns the lowering (one `IWf` over a
  generated member sum, `crates/elab/src/mutual_family.rs`) and the group
  recursion (`crates/elab/src/mutual_rec.rs`). Assumed here: only that the
  group is one `elim_IWf` with a motive by cases on the member.
