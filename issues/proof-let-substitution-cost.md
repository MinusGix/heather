---
title: A proof let is substituted at every use: a let chain checks as one term the size of every copy
status: open
labels: [elaboration,kernel,performance,proofs]
created: 2026-09-25
updated: 2026-09-25
---

A `let` in a proof body is an alias. `statements::elaborate_let` extends the
context with the bound term, and every use of the name is that term. So a
proof written as a chain of `let`s, each using the ones before, reaches the
kernel as one term that holds every copy. The kernel checks each copy where
it occurs, since it has no `let` former.

The certified `wc -l` print profile hit this on 2026-09-25.
`elf64_read_print::read_print_after_read`, written as one body of about
twenty `let`s over the run's intermediate states, took **216 s** to check.
The round split it into three lemmas: `print_formats`, `print_sends` and
`print_writes`. Each is small and the chain is carried by their statements.
The module then checked in about 1.3 s, with no change to what is proved.
Splitting is a fine library style, but a person should not have to find it by
bisection. The next large program will have longer chains.

## Questions

- Where exactly is the copy paid: elaboration (each use re-inferred), the
  kernel gate (each occurrence re-checked), or conversion (a type mentioning
  a bound name compared after it is unfolded)? `--timings` gives the
  frontend/gate split per item. The 216 s item has not been attributed yet.
- What shares the check? Options, cheapest first:
  - elaborate `let x = v; b` as the redex `(λ (x: T) => b)(v)`. The kernel
    checks `v` once (measured linear), but `x` becomes opaque, so it cannot
    serve a let whose value a later conversion needs;
  - lift a large proof `let` to a generated private lemma, which is what the
    round did by hand;
  - a kernel `let` former. That is a kernel design change, and
    `crates/kernel/DESIGN.md` and the DeLaM chapters decide it, not a
    performance issue.
  The first two stay outside the kernel.
- Does the same copy explain [[frontend-large-proof-composition-cost]]'s
  staging gap? If it does, that issue gains its mechanism.

## Acceptance

- The 216 s shape as a regression test or a bench family: a chain of `k`
  `let`s, each using the previous **at least twice** (a chain with one use per
  link is already linear), at growing `k`, in a value form and in a
  transparent form whose later proof lets need the earlier values
  (`refl : s_i = mix(s_{i-1}, s_{i-1})`). Its cost is linear in `k` under the
  chosen fix and is recorded before and after; today both are 2^k (Log,
  2026-09-25).
- `read_print_after_read` written back as one body checks within a small
  factor of the split form, or this issue records why the split is the
  intended style and the diagnostics say so.

## What it assumes from elsewhere

- **[[proof-scale-abbreviations]]** owns surface syntax for sharing across
  declarations. This issue is about the cost of the `let` that already
  exists.
- **[[conjunction-projection-chain-cost]]** is the same round's other shape.
  It may share a cause.

## Log

- 2026-09-25: DIAGNOSED (measurement round, no code changed; furnace, release, `HEATHER_KERNEL_WORKERS=1`). **The cost is a tree/DAG gap, not a per-use copy.** The elaborated term *is* shared in memory: an alias is one `Rc`, and a use at the depth it was bound is `shift_local(0)`, which is a clone of the root. So a chain of `k` lets is a DAG of size `k`. Every consumer after elaboration walks it as a tree, though, so the cost is the number of *paths* through the chain, i.e. the product of the fan-outs along it. It is not the number of uses.
  - **The 216 s item, attributed.** I rebuilt `read_print_after_read` as one body by inlining `print_formats` and `print_writes` (their parameters became lets over `counted`; `print_sends` stayed a lemma). It checked in **186 s at 2 GB, and 96% of that is the kernel gate** (177 s). Against the split form (the four items summed, from `--cache --only`):

    | | queries | misses | eval steps | total |
    |---|---|---|---|---|
    | split (4 items) | 66,235 | 9,348 | 1.15M | 1.1 s |
    | one body | 3,441,953 | 492,298 | 66.7M | 186 s |

    Every count moves by the same **~50×**, which is a tree-size multiplier and not a slower path. The base of that multiplier is `done := counted.witness`: `counted` is the whole `read_loop_counts(…22 args…)` application, and every state `s0…s6` and every proof about a state mentions it. The split turned `done` into a parameter. The split also left each lemma's own lets inlined, which is why it worked: the lemma boundary is **opaque**, so the expensive base became a variable.
  - **Synthetic families** (probe generator not committed; each item is one `fn`/`theorem`; `queries` is the column):
    - `lin`: `let s_i = mix(s_{i-1}, 1)`, one use per link. Linear: 20/36/68/132 at k = 8/16/32/64.
    - `fan`: `let s_i = mix(s_{i-1}, s_{i-1})`. **2^k**: 1,024 / 16,384 / 262,144 / 4,194,304 at k = 8/12/16/20. k = 20 takes 1.5 s and 1 GB for a 20-line function.
    - `redex`: `fan` spelled `(λ (s_i: Nat) => …)(mix(s_{i-1}, s_{i-1}))`. **Linear**: 47/67/87/107. The kernel checks each value once.
    - `dep`: the print shape, i.e. `fan` plus `let p_i: (s_i = mix(s_{i-1}, s_{i-1})) = refl`. 2^k (×4 per +2). **At k = 16 the kernel rejects a correct proof with `OutOfFuel`**, so this is a completeness failure as well as a slow path.
    - `heavy`: one costly `refl` let used `k` times. The gate is linear (0.3 → 3.5 ms at k = 4 → 32). The frontend is superlinear, but that comes from the nested `⟨h, ⟨h, …⟩⟩` conjunction ([[conjunction-projection-chain-cost]]'s shape), not from the let. **Plain reuse of an expensive let is not the problem; fan-out is.**
  - **Where sharing dies, in code** (each is independent; fixing one leaves the others):
    1. **Kernel gate**: `Tc::tm_infer`/`tm_check` (crates/kernel/src/typing.rs:1980) have no memo keyed on node identity, so a shared subterm is re-checked on every path to it, together with its argument conversion queries. This is the whole print item.
    2. **Shift under a binder**: an alias used below its binding depth is `(*a.term).shift_local(by)` per use (crates/elab/src/lib.rs:7625). `map_term` has no per-traversal memo, only the closed-subtree skip in `bounds.rs`, so a shifted DAG comes back as a tree. The print proof's `λ rcx r11 => { … }` continuation pays this.
    3. **Module image**: `put_term` (crates/elab/src/module_image.rs:530) writes a tree with no sharing table, so the image, its node budget and replay are all tree-sized.
    4. **Frontend**: `fan`/`dep` also spend 20–40% outside the gate, and that share grows 2^k too (fan: 1.6 → 39 → 621 ms at k = 12/16/20). **Not located**: `perf` is blocked on the box (`perf_event_paranoid`). The print item's frontend is 4%, so this ranks behind 1–3.
  - **Options, re-costed against the data:**
    - **β-redex** (`(λ x:T. b)(v)`): measured linear, but **opaque**. `x`'s definition is invisible to conversion, so `dep` does not elaborate that way (`refl : s_i = mix(…)` needs `s_i`'s value). The split is evidence that opacity suffices for the print proof. Nothing tells the elaborator which lets need their value, so this is a surface decision (Lean's `have` versus `let`), not a silent lowering.
    - **Generated private lemma**: the same opacity as the redex, plus closure over the context and an image entry. Its only extra is a separately cached, parallel-gated item. It is dominated by the redex unless that matters.
    - **Kernel typing memo on node identity** (keyed on `Rc` address plus context spine, keep-alive entry, the pattern `bounds.rs` already uses): transparent, so it fixes `dep` and the print item without surface change. It is trusted-base state, and does not help cause 2 or 3. It is also the half of [[conjunction-projection-chain-cost]] that re-infers the shared receiver.
    - **Kernel `let` former** (a definitional context entry with lazy ζ): the only option that fixes 1, 2 and 3 together, because sharing becomes syntax that survives shifting and serialization. It is a DeLaM decision: the Coq formalization is edited first, starting with the notions it shares.
  - **Answering the linked question**: [[frontend-large-proof-composition-cost]]'s staging gap is frontend-dominated (68.9 s frontend against 7.5 s kernel), and this item is 96% gate. It is the same family (sharing that does not survive), but a different consumer, so this issue does not give it its mechanism. Its closest cause here is 4.
  - **Acceptance correction**: a chain where each let uses the previous once is already linear (`lin`). The regression family has to fan out: `fan` for values and `dep` for the transparent case the redex cannot serve.
