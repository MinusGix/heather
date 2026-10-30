---
title: Decide what a cast is and how one is written (explicit mark, inferred target)
status: open
labels: [design,elaboration,numerals,tactics]
area: language
created: 2026-10-30
updated: 2026-10-30
---

The library's numeric tower writes its casts five ways (`OfNat(n)`,
`n.int()`, `Rat::ofInt(i)`, `CReal::ofRat(q)`, `d.rat()`), composite casts
have no name, and `omega`, `ring`, `bv_omega` and `intervals` each recognize
casts by their own spelling. `docs/casting-design.md` surveys this and how
Lean, Coq/MathComp, Agda, Idris and Rust handle it, and proposes a standard:
`↑e` as an explicit cast whose target is inferred by the numeral protocol,
only for lossless embedding edges of one cast graph, elaborating to the
composed edge functions (so terms are unchanged), with per-edge law tables
read by one `push_cast`/`norm_cast` family.

Open decisions are §8 of the note: the option (A status quo + tactic,
B explicit mark with inferred target, C B plus leaf insertion in anchored
operator spines), the glyph, which edges qualify, the diamond rule, and the
canonical `Nat → Int` spelling.

## What it assumes from elsewhere

- **docs/carrier-directed-numerals-design.md** owns the numeral protocol.
  Assumed here: only that `operator_carrier_leaf` can classify a new
  checking-only leaf form the way it classifies numerals.
- **[[push-cast-through-embeddings]]** owns the cast-pushing step. Assumed
  here: only that it reads a per-edge law table, whatever the surface.

## Log

- 2026-10-30: Design note drafted (docs/casting-design.md).
- 2026-10-30: Minus objects to combined classes (`CommRingOfInt`, `OrderedFieldOfInt`, proposed `OrderedFieldOfRat`); design §5.6 makes a cast edge a registered morphism value (`OrderedRingHom<A, B>` record of map + laws), generic code takes the morphism as a parameter, and `Int`'s map is derivable by initiality. Agrees with [[interval-containment-once-over-ordered-field]].
- 2026-10-30: DECIDED by Minus: option B, glyph `↑`, and the recommended answer on every other §8 question (edges = numeric tower + Dyadic/Finite first, shortest path + squash, morphism values, `OfNat(n)` canonical). Minus asked for cast tactics better than Lean's push_cast/norm_cast; §6.4 proposes cast-transparent arithmetic tactics (carrier-annotated reification) and `cast_to(S)` (state the goal you want, checked modulo morphism laws) with located `push_cast(at: …)` as the fallback.
