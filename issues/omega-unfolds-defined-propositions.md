---
title: omega skips a goal or fact whose head is a defined proposition
status: closed
labels: [omega,proofs,elaboration,ergonomics]
created: 2026-10-10
updated: 2026-10-12
---

`omega` reads a goal or hypothesis only when its head is already `=`, `<=`,
`<` (or a negation of one) at `Nat`/`Int`. A defined proposition that unfolds
to one is skipped:

```text
fn Rat::Le(x, y: Rat) → Type { x.num * y.den.int() <= y.num * x.den.int() }
theorem t(x: Rat, hx: Rat::zero() <= x): OfNat(0) <= x.num { omega }
-- stuck: hx is not reflected (its head is Rat::Le)
```

The same happens for a goal `x ≈ y` (`Rat::Same`, an `=` underneath), and for
a `Nat` atom such as `Pos::val(Pos::mul(p, q))` that computes to `Succ(…)` of
an expression omega could read. Separately, a fact built as
`Int::cong(λ (t: Int) => e * t, p)` is skipped as "could not spell", while
the same fact written `let f: (e * a = e * b) = cong(p);` is used.

Workaround everywhere in `lib/std/pos.hthr` and `lib/std/num/rat.hthr`: restate the
goal or hypothesis unfolded with a typed `let`, then call omega.

Wanted: before giving up on a hypothesis or goal, whnf it (delta on transparent
definitions, bounded like the other probes) and reflect it if the result has a
relation head. Same for a `Nat`/`Int` atom whose whnf is `Succ`/`OfNat` of a
readable term. Acceptance: the typed restatements in `pos`/`rat` deleted with
the modules still checking, plus a negative control that an opaque (non-
unfolding) proposition is still skipped.

## Log

- 2026-10-12: LANDED. Omega now reads a fact or goal through a defined proposition, a call
  computing to `Succ(…)`/`OfNat(…)`, a field of a call that unfolds to a
  constructor, a factor computing to a numeral, and a `cong` of a function
  literal; design in docs/omega-measure-reduction-design.md §11. Acceptance: the
  typed restatements in `lib/std/pos.hthr` and `lib/std/num/rat.hthr` are gone
  (`Pos::mul_val` keeps its two product facts, which are not restatements), and
  `crates/elab/tests/omega_defined_propositions.rs` covers the rows plus three
  controls: a proposition stuck on a match is still skipped, a false claim
  through a defined fact is refused, and a stuck call stays an atom.
