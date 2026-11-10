# The real line as a locale

Issue: `issues/localic-real-numbers.md`. Modules: `lib/std/locale/presentation.hthr`
(maps out of a presented frame, points read on the basis),
`lib/std/locale/real_locale.hthr` (the line, Heine–Borel, negation),
`lib/std/locale/real_point.hthr` (Cauchy reals as points). Probes:
`lib/_tests/std/locale/real_locale_tests.hthr`. Builds on
`docs/frame-locale-design.md` (frames at `Type<1>`, `Cover`) and on `Rat` and
`CReal` as they stand.

## 1. What this is, and what it is not

The line is presented, not constructed from points: a basis of rational
intervals, two covering axioms, and the cover they generate
(`Cover`, the inductive family of `formal_topology.hthr`). Its frame is the
frame of opens. `CReal` stays the carrier one computes with; the locale is a
second object beside it, whose theorems are about opens and covers, and the
two are tied by theorems (§5), never by a definition. This is what
`localic-real-numbers` asked: no new `Real` carrier, spatiality a conclusion.

What the locale buys is in §4: compactness holds for it outright, where for
the points it needs a choice principle. What makes it pleasant is in §2: a
map out of a presented frame is checked on generators.

## 2. The tool: maps out are checked on generators

A frame presented by an axiom set is the free one on its basis subject to the
axioms. `Cover::hom` is that universal property: a function `g` from the basis
`P` to a frame `B` extends to a frame homomorphism
`u ↦ ⋁ { g(a) | a ∈ u }` (`Cover::extend`) when

- it is monotone,
- it models each axiom, `g(a) ≤ ⋁ g(ax(a, k))` (`Cover::Models`),
- its meets are generated, `g(a) ⊓ g(b) ≤ ⋁ { g(c) | c ≤ a, c ≤ b }`
  (`Cover::MeetsGen`), and the top is, `⊤ ≤ ⋁ g`.

The one induction on covers is `Cover::gen_le` (a covered basic open's image
lies below the cover's), done once here. Everything after it that maps *out*
of a presented locale is finite checking on the axioms: a point (`B = Omega`),
a continuous map into the locale from another (`B` the other's opens), a model
of the axioms in any frame.

**The target is a dictionary value**, `fr: Frame<B>(le, meet, sup)`, not a
section instance. A presented frame is a value built by a function
(`FormalTopology::frame`), which the generic `Frame::…` theorems cannot be
called at (`docs/frame-locale-design.md` §7); a record's own fields can. So
the proof uses fields only, and the target may itself be presented, which is
the case that matters (`RealLine::negation`, a map of the line to itself).

**Points read on the basis.** `FormalPoint<P>(le_p, C, ax, in)` is a point
stated without mentioning an open: a predicate `in` on basic opens that is
closed upwards, lies in a member of every axiom at a basic open it lies in,
meets inside the basis, and is inhabited. `FormalPoint::point` is the `Point`
it is, and `FormalPoint::in_cover` is soundness of covers for points.

## 3. The presentation

`QInterval { lo, hi: Rat }` is the basis, ordered by inclusion of ends. Every
pair is a basic open; one with `hi ≤ lo` is empty and the cover says so.

```
inductive RealAxiom { Shrink, Split(r, s: Rat, h: r < s) }

Shrink at a       : { c | a.lo < c.lo < c.hi < a.hi }
Split(r, s) at a  : { c | c ≤ a  and  (c.hi ≤ s  or  r ≤ c.lo) }
```

`Shrink` says an interval is the union of the nonempty intervals strictly
inside it; `Split` that it is covered by its parts below `s` and above `r`,
which overlap. These are Johnstone's and Coquand–Negri's axioms, in the shape
that suits `Cover`:

- **No emptiness axiom.** `Shrink`'s members are nonempty (`c.lo < c.hi`), so
  an empty interval has none and is covered by nothing (`RealLine::empty`).
  Without that conjunct an empty interval would be covered only by further
  empty ones, a descent with no end, which an inductive cover cannot have.
- **Members are already below `a`.** `Split`'s open is stated as a down-set
  inside `a`, not as two named intervals, so the axioms satisfy the
  localisation condition as they are (`RealAxiom::localised`: below `a`, the
  same axiom at the smaller interval refines it) and the cover is the plain
  `Cover`, with no `LocalAxiom` wrapper to peel in every proof.
- **The axiom type does not depend on the interval**, so `C` is a constant
  family. That cost one elaborator workaround (§8).

`RealLine::frame()` is the frame, `RealLine::Cov(u, a)` the cover,
`RealLine::glue` the split axiom in the form proofs use (two overlapping
intervals cover what they span).

## 4. Heine–Borel, by induction on the cover

`RealLine::compact`: if `a ◁ u`, then for every `lo`, `hi` strictly inside `a`
there is a finite list of members of `u` holding every rational strictly
between `lo` and `hi` (`RealLine::FinSub`).

Constructively this fails for the points of the line unless one assumes the
fan theorem; for the locale it is an induction on the cover, because a cover
is an inductively generated proof and not a pointwise promise. The proof is
Cederquist and Negri's: `Here` is one member; `Down` passes to the larger
interval; `Shrink` picks an interval between the range and `a`; `Split` takes
the two parts' families for ranges overlapping between `r` and `s` and
appends them. The finite cover is stated on rationals (a decidable order), so
gluing two families is one comparison.

**It is a program.** `compact` maps a cover to a list. The probes run it: on
the cover of `(0, 3)` by `{(0, 2), (1, 3)}` it returns those two intervals,
checked by `refl`.

Consequences, each a few lines:

- `RealLine::cover_holds`: a covered interval's rationals lie in members.
- `RealLine::nontrivial`: a nonempty interval is not covered by nothing, so
  the locale is not the empty one. This is the consistency of the
  presentation, and it needs a semantic argument of this kind.
- `RealLine::basic_reflects`: a nonempty interval covered by what lies inside
  `b` is inside `b`. The presentation adds no inclusions between intervals.

## 5. Cauchy reals are points

`x.In(a)` is `ofRat(a.lo) < x ∧ x < ofRat(a.hi)`. `CReal::formal_point` shows
these are a point, and each law is a fact the order on `CReal` already has:

| law | fact |
|---|---|
| `Split` | cotransitivity, `CReal::lt_cotrans` |
| `Shrink` | a rational between apart reals, `CReal::rat_between` |
| meets | the rationals' total order |
| inhabited | `CReal::archimedean`, above and below |

So the two axioms of the line are the two constructive facts about `<`.
`CReal::in_cover` is soundness of covers for reals, `CReal::point_separates`
that apart reals are different points, and `CReal::in_respects` that `≈`
reals are the same point.

**The converse is the next round.** A point gives a real because `Exists` is a
Σ: a point lying in a covered interval *returns* the member it lies in
(`FormalPoint::in_cover`), so a sequence of ever narrower intervals is read
off without countable choice. What it needs is the fine cover (every interval
is covered by intervals of any positive width, `Split` iterated) and the
round trip, `issues/localic-real-points-are-cauchy.md`.

## 6. A first map

`RealLine::negation` is a map of the line to itself, given by
`a ↦ ↓(-a.hi, -a.lo)` and checked on the two axioms (`Shrink` to `Shrink`,
`Split(r, s)` to `Split(-s, -r)`). `CReal::neg_point` says it is negation on
points: the point `-x` is the point `x` followed by the map.

It is here to show the tool at a presented target. Addition and
multiplication need the product locale first
(`issues/locale-products-and-real-arithmetic.md`).

## 7. What makes it nicer, and what it opens

**Tricks that already work.**

- *Covers are data, so their theorems are programs.* Heine–Borel computes a
  subcover; a point returns the member it lies in. Nothing is truncated
  (`docs/frame-locale-design.md` §2), so every existence proved by induction
  on a cover can be run or read.
- *One induction, then finite checks.* After `Cover::gen_le`, a map or a
  point is a case split over `RealAxiom`'s two constructors.
- *Sublocales cost no new type.* A nucleus changes the order on the same
  carrier (`Nucleus::frame`), so `[0, 1]`, an open interval, or a complement
  is the line's opens at another order index.

**Tricks within reach.**

- *Interval arithmetic is the basis-level data of a map.* `x.In(a)` is what
  the float library's enclosures prove (`HasReal`). An interval extension
  `F` of `f` with its containment theorem gives the relation "`F(a)` lies in
  `b`", which is the generator data `Cover::hom` asks for. So every function
  with a verified enclosure is a continuous map of locales, and the interval
  tactic's output is a candidate proof of continuity.
- *Finite covers are decidable.* Whether finitely many rational intervals
  cover a rational interval is a computation, so `a ◁ u` for a finite `u` can
  be a closed verdict (`b = True` by `refl`), with Heine–Borel's converse as
  the soundness theorem (`issues/interval-cover-decision.md`).
- *Compactness as a quantifier.* With `[a, b]` compact, "for all `x` in
  `[a, b]`" of an open property is itself open, and continuity on `[a, b]`
  gives uniform continuity as a theorem. `closed_interval.hthr` takes the
  modulus as a hypothesis today; the localic statement derives it
  (`issues/closed-interval-compact-sublocale.md`).
- *A real varying over a space.* A frame homomorphism out of the line's
  frame into `O(X)` is a continuous real function on `X`; the same data in
  `Omega` is a real number. Anything proved from the axioms alone holds for
  both, which is how one proof serves numbers and functions.

**Areas, in the order they would pay.**

1. *Points are exactly the Cauchy reals* (§5). The first acceptance of
   `real-presentation-comparison`: a nontrivial map, both ways, with its
   assumption inventory (none: no choice, no excluded middle).
2. *Products and arithmetic.* The product of presented locales is presented
   on pairs of basic opens; addition and multiplication are maps out of it.
3. *The closed interval*: compactness as a statement about its frame, uniform
   continuity, suprema of continuous functions.
4. *One-sided reals.* The same machinery with only lower ends presents the
   lower reals (`lower-real-numbers`); a Dedekind real is a lower and an
   upper one that fit. Lower reals are where valuations take values.
5. *Valuations and integration.* A valuation on a locale assigns lower reals
   to opens; integration over `[0, 1]` and then measure follow Coquand and
   Spitters and Vickers. This is the constructive road to measure the
   roadmap names.
6. *Other presented spaces by the same tool.* Cantor and Baire space (basis:
   finite prefixes; axiom: split on the next symbol) are compact or
   bar-inductive for the same reason the line is, with no fan theorem
   assumed, which bears on streams, `CoTree` and interaction trees: a
   continuous function on streams is uniformly continuous, as a program. The
   Zariski spectrum of a ring (basis: elements; covers: generated ideals)
   gives prime-ideal arguments without prime ideals.

## 8. What the language resisted

Little: the modules were written against the `Cover` family and the frame
classes as they are. Three things were worked around and filed.

- **An implicit that is a constant family was not inferred** from a record
  type whose fields apply it (`issues/implicit-constant-family-record-parameter.md`,
  since fixed). `FormalPoint<QInterval>(…, λ a => RealAxiom, …)` has `C(a)`
  reduced away in its field types; the unifier now solves the Miller pattern
  `?C(a)` by abstraction (`docs/unifier-completeness-design.md` §10.4), and
  `FormalPoint::point` and its theorems take the presentation implicitly.
- **`linarith` at `Rat` without `ordered_field` imported** reads the goal at
  `Int`, through numerators and denominators, and fails with that reading
  (`issues/linarith-rat-without-ordered-field-import.md`). Fixed
  2026-11-10: the common prelude imports `ordered_field`, so `import rat;
  import linarith;` is enough.
- **`QInterval.rel_trans(…)`**, a class member at a carrier whose relation
  index nothing in the call pins, is refused with a clear message; the module
  states `QInterval::le_trans` as a theorem. Not filed: the message says what
  to do.
