---
title: ITy widened tm_infer's return and tm_check's argument; nat/check-numeral pays 1.4x per node
status: closed
created: 2026-09-20
updated: 2026-09-20
---

**Status:** closed — **attacked, and the attribution below is the answer**:
it was never the width of anything, it was 86 constructed temporaries in the
*checking* direction and one arm's view sitting in every frame of the
recursion cycle. Three changes, in `crates/kernel/src/typing.rs` and
`typing/ity.rs`; the bench gate is clean and the corpus is back inside its
own spread. Filed by
stage 1b of `docs/intro-by-type-design.md` as the residue of its own bench
gate, per `issues/README.md`'s rule that a regression worth keeping gets an
issue. Originally filed as: measured, unattacked. Filed by stage 1b of
`docs/intro-by-type-design.md` as the residue of its own bench gate, per
`issues/README.md`'s rule that a regression worth keeping gets an issue.

## The number

`scripts/bench --check` on a quiet desktop (load 1.9), after stage 1b's
`ITy`:

```
 REGRESSED  nat/check-numeral:64      1.47 µs →  2.16 µs (1.47×)
 REGRESSED  nat/check-numeral:128     3.19 µs →  4.42 µs (1.39×)
 REGRESSED  nat/check-numeral:256     6.41 µs →  9.27 µs (1.45×)
 REGRESSED  nat/check-numeral:512    14.96 µs → 21.18 µs (1.42×)
 REGRESSED  stack/check-numeral depth  1512 → 1341 levels in 4 MiB (3128 B/level)
```

Everything else the harness gates is **inside tolerance**, including the two
that measure the same checker over bigger objects: `wf/check-tree`,
`code/check-identity-recursor`, and `check/generated-terms` — the broad
checker-throughput row — all pass. So this is a **per-node constant on the
narrowest possible workload**, not a slope and not a whole-workload cost. The
routine corpus agrees: `lib/ir_v1`, `probes/t_cp9`, `probes/t_qt3`,
`probes/str/p10` all landed inside their own before-against-before spread
(issue log, 2026-09-20).

## Where it comes from

Stage 1b widened two channels of `typing.rs`:

- what `tm_infer` **returns**: `Type` → `ITy` (`Type` plus a tag);
- what `tm_check` **takes**: `&Type` → `&ITy`.

`nat/check-numeral` checks `Succ^n Zero : Nat`, so its entire body is one
`tm_infer` and one `tm_check` per node with almost nothing else in between —
which makes it the one benchmark where that widening *is* the measurement.
The stack row is the same fact seen from the other side: one `ITy` per level
instead of one `Type`, and `tm_check`'s extra wrapper, is +358 B per frame.

Two rounds of this were already paid down and are **in** the numbers above:

1. The first shape, `ITy::Syn(Rc<Type>)` alone, boxed every inferred type and
   cost **4.15×** here. `ITy::Owned(Type)` — the value the rule already had
   on its stack, moved rather than allocated — took it to 1.64× and fixed
   `wf/check-tree` (1.29× → inside) and `code/check-identity-recursor`
   (1.33× → inside) outright.
2. `#[inline(always)]` on the two `tm_check` wrappers took it to 1.42× and
   recovered 46 stack levels.

## What is left to try, if it is worth trying

- **A borrowing expected type.** `tm_check` never stores its expected type,
  so `ITyRef<'a> = Syn(&'a Type) | Sel(&'a ITy)` would make the checking
  direction — the common one — construct nothing at all. The cost is a
  lifetime through the checker and a second small type beside `ITy`.
- **A narrower `ITy`.** Boxing the `Sel` payload does not help (it is already
  the small arm); shrinking `Type` would, and is a different round.
- **Nothing.** The honest option. A 1.4× per-node constant on a checker that
  this round is about to make asymptotically cheaper may simply be the right
  trade, in which case the move is `scripts/bench --save` with this issue as
  the record of what was traded and why — which is the coordinator's call,
  not the implementer's.

## Do not re-diagnose from a loaded box

The first attempt at these numbers ran while another session was using the
main checkout at ~200 % CPU, and produced a before-against-before spread
(4.87 → 7.36 CPU-s on `ir_v1`) wider than any of the deltas above. The rows
here were taken at load 1.9. See `desktop-bench-gate-for-constants`.

## The corpus split, on a quiet box (2026-09-20, after the two fixes)

The microbenchmark said "per-node constant". The corpus says the same thing
from the other side, and the sign of the delta is decided by **what the file's
time is made of**:

| file | before CPU-s | after CPU-s | | what dominates it |
|---|---:|---:|---|---|
| `lib/ir_v1.hthr` | 3.94 | 5.26 | **+33 %** | many small declarations — inference per node |
| `probes/t_cp9.hthr` | 34.07 | 41.13 | **+21 %** | ditto, with a record tower |
| `probes/t_qt3.hthr` | 49.75 | 62.72 | **+26 %** | ditto, deeper |
| `probes/str/p10.hthr` | 118.75 | 113.65 | **−4 %** | 42 M conversion queries |
| `complete_post` (`--only`) | 17.21 | 14.54 | **−16 %** | conversion, over a replayed prefix |

Peak RSS across the same five: −0.1 % to +4.1 %, no direction.

So the widening is paid once per *term node*, and a workload whose time is
conversion does not notice it — `p10` and `complete_post` are, if anything,
faster. That is the shape a fix should preserve: whatever replaces the
`ITy` in the checking direction must not slow the conversion path down to buy
back the inference one.

It is also the reason the number matters less than it looks: stage 2 of
`docs/intro-by-type-design.md` exists to move the tower's cost *out* of the
per-query conversion work, and the files that pay this constant are the ones
whose declarations are small enough that nothing else is happening.


---

## 2026-09-20 — attribution, before any edit

Two instruments, both **load-independent**, which is why they could be taken
on a box at load 12–18 while another session held the machine:
`std::mem::size_of` out of a throwaway example, and the `sub $N,%rsp` of each
`Tc::` symbol out of `objdump` on the release rlib, taken on both
`9c16741` and `f4328bd`.

### The width hypothesis is dead

```
crate::term::Type                72     ITy                              72
Arc<Type>                         8     Sel                              16
(Type, Level)                    96     (ITy, Level)                     96
R<(Type, Level)>                 96     R<(ITy, Level)>                  96
                                        TyForm                          200
```

`ITy` is **exactly `Type`'s size** — the tag rides in a niche — so widening
`tm_infer`'s return cost zero bytes, and neither the return nor the wrap is
the regression. Every shrink-the-return idea on this issue's list was aimed
at a channel that had not moved.

### What did move: frames on the recursion cycle

`sub $N,%rsp`, in bytes, for the symbols that changed:

| symbol | 9c16741 | f4328bd |
|---|---:|---:|
| `tm_check` | 296 | *inlined away* |
| `tm_check_inner` | *merged into `tm_check`* | **712** |
| `tm_infer` | *inlined away* | **96** |
| `tm_infer_inner` | 2360 | 2296 |
| `conv_ty` | 696 | 712 |

The checker's recursion cycle is one `tm_infer_inner` and one checking frame
per term node. Before: 2360 + 296 = 2656. After: 2296 + 712 + 96 = 3104.
With the pushes the probe sees that is 2774 → 3128 B/level, which is the
stack row exactly. So the whole per-node constant is **`tm_check_inner`
growing 296 → 712**, plus `tm_infer` falling out of line.

### Why each grew

- **`tm_infer` fell out of line.** Before stage 1b it was a tail call with
  its callee's own signature, so LLVM merged the two. The `@` dispatch and
  the `ITy::Owned` wrap made it a non-tail call; it got its own 96-byte frame
  *and* two 96-byte copies of the inferred `(type, level)` per term node.
- **`tm_check_inner` grew by 416 bytes.** `tm_check_rc` and `tm_check_ty` are
  `inline(always)`, so each of their **86 call sites** (62 `_ty`, 24 `_rc`)
  built a 72-byte `ITy` temporary *in the caller's frame* — and the `_rc`
  ones paid an `Arc` increment and decrement per term node on top, which is
  the routine corpus's share and not the microbenchmark's. On top of that the
  λ arm's view went from a 72-byte `Type` to a **200-byte `TyForm`** whose two
  `ITy` components it then holds across its own recursive descent.

So the per-node delta is: one extra non-inlined call, two 96-byte copies, an
`Arc` pair per checked subterm, and 354 more bytes of stack touched per level.

## 2026-09-20 — attempt 1: `#[inline(always)]` on `tm_infer`

Restores the pre-stage-1b shape: the `@` dispatch and the wrap fold back into
the callers, the 96-byte frame and both copies go.

Verified structurally — `tm_infer` is gone from the symbol table — and
**neutral on the stack row: 1341 levels, unchanged to the unit**, because
`tm_check_inner` simply absorbed the 96 bytes. Kept anyway: it removes a call
and two 96-byte memcpys per term node, which the stack probe cannot see.
Not the fix.

## 2026-09-20 — attempt 2: `ITyRef`, the borrowing expected type

The candidate this issue named, in the shape the code wanted:

```rust
pub(crate) enum ITyRef<'a> { Syn(&'a Type), Ity(&'a ITy) }
```

Two words, `Copy`, built by a tag write. `Tc::tm_check`, `tm_check_inner`,
`conv_ty`, `conv_ity`, `whnf` and `view_expected` take it; `tm_check_rc`
passes `ITyRef::Syn(ty)` with **no `Arc` clone** and `tm_check_ty` passes
`ITyRef::Syn(ty)` with **no `Type` clone**, so all 86 sites construct
nothing. `Tc::view`'s syntactic branch is split out as `view_syn` so a
borrowed bare spelling — which is never a selection — reaches it without an
`ITy` having to exist. The one place that pays back is `conv_ity`, which is
the `@` path only and off the constant entirely.

```
tm_check_inner   712 → 664      conv_ty  712 → 680      tm_infer_inner  2296 → 2280
stack/check-numeral    1341 → 1370 levels      3.0 KiB per level
```

Real, and a quarter of the gap. The temporaries were not the bulk.

## 2026-09-20 — attempt 3: outline the checking λ

The residue was one arm. `Tc::tm_check_inner` matches nine term shapes, but
the checker *recurses* through exactly one of them — the `_` fall-through
that infers and converts — while the λ arm is the one that takes a 200-byte
`TyForm` and holds both of its `ITy` components across its own descent.
Inline, those temporaries sit in every frame of the recursion cycle whether
or not a λ is being checked. Outlined as `Tc::tm_check_lam`,
`#[inline(never)]`:

```
tm_check_inner   664 → 312   (9c16741's tm_check was 296)
tm_check_lam     (new, off the cycle)                  616
tm_infer_inner                                        2280   (9c16741: 2360)

stack/check-numeral   1341 → 1548 levels    2.6 KiB per level
                      baseline 1512 — the row is a PASS, and past it
```

Cycle: 2280 + 312 = 2592 against `9c16741`'s 2656. The checker now recurses
in a *smaller* frame than before `ITy` existed, which is the honest reading
of why this was never an `ITy` cost: `ITy` is free, and the checking
direction had simply stopped borrowing.

## 2026-09-20 — the gate, on a quiet box

`scripts/bench --check`, verbatim, at **loadavg 2.76** (4.35 when it
finished):

```
ok: 112 comparisons within thresholds
```

The two rows that failed:

```
nat/check-numeral:64      1.47 µs → 1.72 µs   (was 2.16 µs, 1.47×)
nat/check-numeral:128     3.19 µs → 3.64 µs   (was 4.42 µs, 1.39×)
nat/check-numeral:256     6.41 µs → 7.60 µs   (was 9.27 µs, 1.45×)
nat/check-numeral:512    14.96 µs → 17.65 µs  (was 21.18 µs, 1.42×)
stack/check-numeral      1512 → 1548 levels in 4 MiB (2.6 KiB/level; was 1341)
```

The stack row is now **above** the baseline. The numeral row keeps a residual
1.17–1.19×, inside the harness's threshold — what is left there is the design
itself and not an accident: `tm_infer`'s five-way `@` dispatch, and an
expected type that is two words where it used to be one. The baseline is
**not** re-recorded; the committed one is what this passes against.

## 2026-09-20 — the corpus, same box

`scripts/perf ab --base 9c16741 --samples 3`, cold, width 1, loadavg
`[3.86, 6.56, 10.85]` (the one-minute figure is the decay of the bench run
that preceded it; the box was otherwise idle and the three samples of each
file agree to within a per cent):

| file | median wall | verdict | stage 1b had it at |
|---|---:|---|---:|
| `lib/ir_v1.hthr` | −0.9 % | **no change** | +33 % |
| `probes/t_cp9.hthr` | +0.2 % | **no change** | +21 % |
| `probes/t_qt3.hthr` | −0.7 % | **no change** | +26 % |
| `probes/str/p10.hthr` | +0.3 % | **no change** | −4 % |

`kernel_gate` agrees on all four (−0.9 %, +0.4 %, +0.3 %, −0.2 %), and peak
RSS moves by −0.0 % to +0.0 %. On every file, every sample, both binaries:

```
counters — nothing moved
identical across both binaries and every sample: 29 columns
```

So the constant is gone from the routine corpus and the conversion-dense
files did not pay for it, which was the shape the fix had to preserve. The
checker's behaviour is unchanged to the unit, as it was at stage 1b.

**Verdict: closed.** The design is untouched — `ITy` is still the checker's
currency, `Sel` is still arena-free, and nothing moved in
`docs/intro-by-type-design.md` §3.2–3.4. What changed is that the *checking*
direction borrows instead of owning, and the one arm with wide temporaries is
no longer on the recursion cycle.

Correctness, same tree: `scripts/test` (full lane) is
`== suite: 2835 passed, 0 failed, 5 ignored ==` — the count stage 1b
reported — with `typing_differential`, `conv_differential`,
`eval_differential` and `ch05_06_lemmas` all green.

## Two notes this round was asked to leave

- **`--features value-metrics` is now checked by the suite.** It is the
  diagnostic build — the `--timings` value counters, the conv-miss sampler,
  the `diag_enter` frames — and no test target compiles it, so it rots
  silently and did (it did not build at `9c16741`). `scripts/test` now runs
  `cargo check -p heather-kernel --features value-metrics` beside the
  tree-sitter inventory check: seconds, and a *check*, because the feature
  changes instrumentation and not judgments.
- **`probes/` stays untracked**, as it is in the main checkout. Three rounds
  have now measured against it, which is the argument for committing it, and
  that is a decision for the handover on
  `elab-emits-normal-form-of-matched-type-argument`, not for this issue.
