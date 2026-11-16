---
title: A tactic for computed native obligations (Wp, Stretch, Straight)
status: open
labels: [tactics,native,proofs]
area: tactics
milestone: [hih-program-logic]
created: 2026-10-20
updated: 2026-10-20
---

A tactic that discharges the routine part of a computed obligation
(`Wp`, and `Stretch`/`Straight` until they are its instances; design
`docs/native/native-program-logic-design.md` §8–9).

A caller's term against a computed obligation is the same shape every time:
an `Exists` per slot, page offset, loaded word or byte whose witness
conversion already knows (the base register's value, `refl` where a block
set it), a pair per `Jcc` whose sides are either absurd from a flag fact or
handed to the caller, a λ per leaf binding the end state. The command's
phases, the filter's loops and the argument scan each write it by hand
(the "third time" rule of `docs/roadmap.md`'s "Tactics everywhere").

Wanted: a tactic that walks the computed type, introduces the leaves and
the JCC sides as goals, picks witnesses that the address equations fix by
`refl`, and closes a flag side by `decide` or `bv_omega` when the
precondition decides it. It must not spell the type's whnf in a diagnostic
(the error-path rule), and it should be written in Heather once
`tac-host-interface` lands, so it is a candidate for `tac-first-port`'s
successor rather than a new Rust tactic.

Since the 2026-10-21 revision these obligations arise in the compiler's
per-construct lemmas over abstract inputs rather than in every program, so
there are far fewer of them. File the work only if those rounds write the
shape by hand a third time.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns the obligation's shape.
- **[[host-elaboration-interface]]** owns how Heather code reads a goal.
