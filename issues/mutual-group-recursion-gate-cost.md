---
title: Structural recursion over an m-member mutual group costs about m^2.8 in the gate, and runs out of fuel at eight members
status: closed
labels: [kernel,elaboration,inductives,performance]
area: language
milestone: [math-metatheory]
created: 2026-10-26
updated: 2026-10-27
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

## Log

**2026-10-26 — the refl checks, and the group is about quadratic.** On
master after [[indexed-family-recursion-gate-cost]]'s round (PR #202), plus
this round. `heather check --timings`, release, width one, cloud box,
`size0` total / gate, and the `refl`'s gate:

| m | before both | master (#202) | this round | `refl` now |
|---|---|---|---|---|
| 4 | 1,475 / 1,427 ms | 1,024 / 986 ms | 46 / 30 ms | 5 ms |
| 8 | 13,629 / 13,432 ms | 7,470 / 7,321 ms | 135 / 82 ms | 11 ms (was `OutOfFuel`) |
| 12 | — | 23,439 / 23,012 ms | 371 / 229 ms | — |
| 16 | — | — | 692 / 395 ms | — |

About m^2.3 in the gate from 8 to 16, against m^2.8 before.

1. **The `refl` ran out of fuel comparing two steps**: the ih β handed the
   step was `iwf_ih`'s λ, whose body holds a shifted copy of the step, so
   closure identity missed and conversion unfolded the step's whole case
   tree. Found here and fixed by `Val::IWfIh`, which PR #202 landed first
   with the same shape; this round adds its readback (as `iwf_ih`) and a
   kernel test at a neutral index (`crates/kernel/tests/iwf.rs`).
2. **The signature was judged at every occurrence.** The typing memo keys
   on Γ, so an `IWf(sig)(…)` met under each arm's binders re-judged the
   signature, Θ(m²) apiece. The kernel now keeps locally closed types and
   signatures in a memo apart from Γ (`ty_check`, `iwf_sig_wf`; closedness
   decided by the bounds metadata at a node's second sight). It hit nothing
   at first: the output and child trees' leaves were `inl@`/`inr@`
   annotated at `El(u^{·^k})`, a global reference whose tail records |Γ|,
   so no signature was locally closed, and neither were the motives that
   spell it. The elaborator now leaves an index leaf unannotated (it is
   checked against the index type anyway). With the leaves tail-free, PR
   #202's strengthened scopes (a node keyed by the innermost entries it
   reads) hit on the step's per-level convoy motives too, which is what
   took the cubic off; with this round's closed memo off the same build
   asks about 20× the conversion queries at m = 12.
3. **The `Case`/`elim_Nat` rules instantiated their motives through an
   identity substitution**; `inst_top` now (counters unchanged).
4. **λ domains copied from the expected Π were judged and converted
   again.** The expected type is presupposed well-formed, so a λ whose
   domain is spelled as the expected domain skips both (`tm_check_lam`),
   except while recording spellings for an export, which reads the
   domain's own spellings off that judgment.

What is left is about quadratic: each of the step's Θ(m) arms still meets
types spelling the Θ(m) member sum. The acceptance's slope "towards 1" is
not reached; whether quadratic is enough for the heather-coq port (a group
of seven: about 75 ms of gate) is the question for whoever picks this up
next, so the issue stays open.

**2026-10-27 — the signature is named; closed.** The signature's index
functions are generated definitions (`D#iarity`, `D#iout`, `D#ichild`), and
the step's ih type is spelled with a fourth (`D#idnth`), so a member wrapper
or a convoy motive carries a handful of references where it carried the
Θ(m²) trees (`docs/inductives/iwf-named-signature-design.md`). `heather check
--timings`, release, width one, cloud box, `size0` total / gate, and the
whole file:

| m | master (#205) `size0` | now `size0` | master file | now file |
|---|---|---|---|---|
| 4 | 36 / 24 ms | 8 / 5 ms | 49 ms | 24 ms |
| 8 | 137 / 80 ms | 26 / 16 ms | 154 ms | 55 ms |
| 16 | 582 / 316 ms | 55 / 35 ms | 604 ms | 93 ms |
| 24 | 1,653 / 806 ms | 114 / 75 ms | 1,682 ms | 172 ms |

Each member's declaration now pays for the definitions it registers (`M0`
grows from a few ms to tens, linearly). `inductive/mutual-recursion`
re-recorded from below at 0.95 over 2..8 (fixed cost dominating);
`inductive/mutual-declaration` at 1.02. By hand from 24 to 160 members the
group is about m^1.8: the step's case tree is a comb over the shape spine,
Θ(m) deep, its motives hold the label as an `inr` chain of that depth, and
each arm evaluates the definitions down the same chain. That is the
constructor encoding of every inductive, filed as
[[iwf-shape-spine-comb-depth]] rather than kept here. (Merged with PR #214's balanced sums the
same day: 160 members 6.1 s → 4.4 s, still about m^1.6; that issue now
tracks the residue.)
