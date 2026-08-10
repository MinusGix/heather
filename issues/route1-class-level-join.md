---
title: A route-1 family with level-heterogeneous classes is unusable
status: closed
labels: [elaboration, inductives, levels]
code: crates/elab/src/indexed.rs @ 132731d
created: 2026-08-06
updated: 2026-08-10
---

A route-1 indexed family whose index classes do **not** all reach the
family's join level is rejected by the kernel with `LevelMismatch` at every
use. Minimal reproducer (rejected on master; predates and is unchanged by
the `D#fam` round):

```text
inductive V : (n: Nat) -> Type {
    V0                                 : V(0),          // class at level 0
    V1(n: Nat, A: Type, x: A, t: V(n)) : V(Succ(n)),    // class at level 1
}
```

`fam_class` builds each class code at its *own* level (tag spine
terminating in `Type::Unit { level: Level::Zero }`, field levels joined per
constructor) while the family's motive is `Ty l` with `l` the join over
**all** classes — and there is no cumulativity to bridge a level-0 class
into a `Ty 1` motive.

Every nonzero-level fixture in the suite hid it by giving *every*
constructor a `Type`-valued field, so all classes landed at one level
(`fields_above_level_zero` is one field away from the failing shape).
Found 2026-08-06 while building the level-1 fixture for the `D#fam` round
([[indexed-families]]), which routes around it by keeping its classes
level-homogeneous. Full writeup with the failing shape and fix direction:
`docs/inductive-indexed-lowering.md` §10.5.

**Fix direction** (from that writeup): build every class code at the
family's `l` — the formers all take a level (`Type::Unit { level }`,
`Type::Sigma`, `Type::Sum`), so it is a threading change, not a theory
change. But it changes the emitted type of every route-1 family, so it is
its own round, with the fixture that varies class levels *asymmetrically*
as the acceptance test the suite currently lacks.

Today's symptom ordering: such a declaration's `D#fam` fails the
registration gate (occurrence inlines, best-effort as designed), and the
declaration was unusable before the gate ever saw it.

## What it assumes from elsewhere

- **[[indexed-families]]** owns the route-1 scheme. Assumed here: only that
  the family motive is `Ty l` at the join over classes.

## Log

- 2026-08-06: Filed, off the `D#fam` round's level-1 fixture work.
- 2026-08-10: LANDED: route-1 constructor spines now terminate at the family join (`Unit^l`), so every class code inhabits the shared `Ty l` motive while payload fields retain their own levels. The asymmetric `V0`/`V1(A: Type, x: A, ...)` fixture now constructs values at both indices and pins route 1; adjacent indexed suites and full `scripts/test` are green.
