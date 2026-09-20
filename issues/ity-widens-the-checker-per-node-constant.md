---
title: ITy widened tm_infer's return and tm_check's argument; nat/check-numeral pays 1.4x per node
status: open
created: 2026-09-20
updated: 2026-09-20
---

**Status:** open, measured, unattacked. Filed by stage 1b of
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
