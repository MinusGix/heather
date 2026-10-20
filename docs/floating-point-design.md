# Floating point: a design for Heather

Status: design, 2026-10-20. Minus reviewed the first draft the same day and
settled most of its questions; §9 records the answers and the few points
still open, and §3.1, §4 and §5.5 were written in response to the review.
No code yet. Owns the roadmap milestone `math-float` and its submilestones
(`docs/roadmap.md`); tracking issue
[floating-point-formalization](../issues/floating-point-formalization.md).

The starting point is Minus's Lean library, **flean**
(github.com/MinusGix/flean, read at its default branch on 2026-10-20: about
99k lines over 112+ files, sorry-free). It covers all five IEEE rounding
modes, add/sub/mul/div/sqrt/fma with "result = round(exact)" theorems,
the error-free transformations (Fast2Sum, TwoSum, TwoProduct, Veltkamp,
Sterbenz), Kahan/Neumaier/compensated summation, double-double arithmetic,
correctly rounded `exp` and `log`, the OCP 8-bit storage formats, bit-level
encode/decode, and a long tail of ML numerics (softmax, layer norm, GELU,
dot products). The instruction is not to port it line for line: keep what it
got right, fix what it got wrong, and lean on what Heather already has
(`Rat`, `CReal`, the ordered-field and semiring classes, `BitVec`,
searched evidence, proofs by evaluation).

## 1. What flean gets right, and Heather keeps

- **The semantic core is value-level, not bit-level.** A finite float is a
  sign, an integer significand and an exponent; bits are a separate
  encoding with a round-trip theorem. This is Flocq's choice too, and it is
  the right one: every proof about rounding lives on integers.
- **The correctness statement for an operation is "the result is the
  rounding of the exact result"** (`fpAddFinite_correct`: `a + b = ○(a.val +
  b.val)`). Every later error bound is a corollary of this plus a bound on
  the rounding.
- **One integer rounding routine does the work for every operation**
  (`roundIntSigM`: sign, magnitude, exponent, plus sticky information from
  division and square root). Operations reduce to "compute the exact value
  as an integer times a power of two, perhaps with a sticky bit, then
  round".
- **The error-free transformations and the summation analyses** are the
  part of the library downstream users (GPU, ML) actually cite. They should
  port nearly as stated.
- **Storage formats are first-class**, with saturating/NaN-only/no-infinity
  policies, because ML and GPU work needs E4M3, E5M2 and friends.
- **Exp and log terminate by an irrationality gap.** `ExpTermination.lean`
  proves via Padé approximants that `exp(x)·2^s` stays a computable
  distance away from every integer, so the Ziv-style refinement loop stops.
  That idea is exactly what the constructive story in §5 needs, and it
  carries over.
- **No `native_decide`, no hidden `sorry`.** Heather's kernel gives this by
  construction; proofs by evaluation replace `decide`.

## 2. Where flean's design hurts

Each item names the symptom in flean and the Heather fix, which §3–§7 then
spell out.

**P1. The format is an ambient typeclass.** `class FloatFormat` carries
`prec`, `min_exp`, `max_exp`, and every type (`FiniteFp`, `Fp`,
`FloatBits`) takes `[FloatFormat]` without naming it. A file has one format
at a time; mixed precision needs a tower of `letI`s with explicitly
`@`-applied instances (`StorageFormats/MixedPrecisionOps.lean`:
`letI : @RMode R ff_wide := …`, five in a row). `Binary32` is a *value of
the class type* activated by `local instance`. Minus's own sketch
("Sketch idea of an alternative structure") already reaches for
`Fp (F : FloatDesc)`. *Fix:* the format is ordinary data and an explicit
index of the type: `Float(binary32)` and `Float(e4m3)` are different types
in one scope, and conversion is a function between them (§3).

**P2. Precision is an `ℤ`, so `toNat` is everywhere.** `prec : ℤ` with
`valid_prec : prec ≥ 2` spawns a page of `prec_toNat_*`,
`prec_sub_one_toNat_*` and `natCast_pow_*` lemmas in `FloatFormat.lean`
alone, and three custom tactics (`linearize` at ~356 sites, `bound_calc`
~144, `zpow_norm` 46) exist mostly to fight `zpow`/`pow` and cast
mismatches. *Fix:* precision is a `Nat` with its lower bound as searched
evidence (`Pos`-style, `docs/positivity-evidence-design.md`), exponents are
`Int`, significands `Nat`, and the value of a float is computed through a
**dyadic** (`Int` mantissa, `Int` exponent) whose comparisons reduce to
integer shifts, so `omega` closes what flean needed `linearize` for (§4).

**P3. The stored exponent is the leading exponent.** Flean stores `e` with
value `m · 2^(e - prec + 1)`, so `e - prec + 1` appears in nearly every
formula and every proof. *Fix:* store the **quantum exponent** `q` (the
exponent of the last significand bit) with value `m · 2^q`, as Flocq does.
The leading exponent is a derived function for the few places IEEE's
spelling matters (encoding, `logB`).

**P4. Too many float types and two format descriptions.** Per format there
are `FiniteFp`, `Fp`, `InfFp`, `FloatBits`, `FloatBitsTriple`,
`FpQuotient`, and separately `StorageFormat`/`StorageFp` with its own
layout fields; converting a `StorageFormat` into a `FloatFormat` takes three
proofs (`sf.toFloatFormat h_prec h_bias h_exp`). *Fix:* one `Format`
record covers IEEE interchange formats and the OCP storage formats, with
the special-value policy as data; one semantic type `Float(F)`; one
encoding, derived from the format (§3, §7).

**P5. Equality, value equality and order are tangled.** `FiniteFp` has two
zeros, so `=` is not value equality; its `LinearOrder` instance is a
*structural* order in which `-0 < +0`, and the IEEE order is a second
relation `stdLt`; which one `≤` should mean is still open (flean issue
#15). *Fix:* use Heather's setoid convention. At `Finite(F)`, `≈`
designates value sameness and `<` the value order, so a finite float is a
`StrictOrder` instance like `Rat`; `=` stays structural and never gets an
order symbol. IEEE `compare` (with unordered NaN) and `totalOrder` are
named functions at `Float(F)` (§4).

**P6. Rounding is defined twice and glued by classes.** The specification
`roundDown x := findPredecessor x` searches over a generic `R` with
`[Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]` using
`Int.log`; the executable rounding is `roundIntSigM` parameterised by
`RModeExec` hooks; and they meet through `RModeExecSound`,
`RoundIntSigMSound` and `RModeSticky`. `fpAddFinite_correct` takes eight
instance arguments. *Fix:* the specification is a **relation**
(`RoundsTo(F, mode, x, r)`: order facts only), there is **one** executable
rounding on dyadics with a sticky flag, and one theorem says it satisfies
the relation (§5).

**P7. The rounding mode is typeclass context, with sixteen classes.**
`RMode`, `RModeZero`, `RModeMono`, `RModeIdem`, `RModeC`, `RModeConj`,
`RModeGrid`, `RModeNearest`, `RModeExec`, `RModeExecSound`,
`RModeTieEven`, `RModeTieAway`, `UseRoundingPolicy`, `RModePolicyTag`,
`RModePolicySpec`, `RModeSticky`, plus five marker types. One mode is
active at a time, like the format. *Fix:* `Mode` is an enum value passed
as an argument (defaulting to nearest-even, `named-arguments-design` §9.6);
mode laws are theorems proved by cases on the mode. Only a genuinely
generic statement ("any monotone, idempotent rounding…", which stochastic
rounding and round-to-odd also satisfy) quantifies over a `Rounding`
record (§5.4).

**P8. The value domain is generic in `R` and classical.** `toVal` needs
`(R := R)` annotations everywhere, `FloorRing` and `LinearOrder` are
assumed, and ERat/ENNRat were built as a computable codomain on the side.
None of it is constructive: rounding is discontinuous, so `roundDown :
ℝ → Fp` is not a computable function at all. *Fix:* the one canonical
value is exact and computable (`Dyadic`, embedded in `Rat`); rounding
*computes* only from dyadics (plus sticky) and from `Rat`; statements over
any ordered field (in particular `CReal`) go through the relation, and
computing the rounding of a real takes the evidence that makes it
computable: apartness from the rounding breakpoints (§6).

**P9. Correctness theorems carry special-case side conditions.**
`fpAddFinite_correct` assumes `a.val + b.val ≠ 0` because the zero case is
the signed-zero rule. *Fix:* split every operation's theorem into a
value part (the result `RoundsTo` the exact value, no side condition) and
a sign-of-zero part, so error analyses never meet the zero rule.

**P10. Missing IEEE semantics.** Exception flags, NaN payloads and
quiet/signalling NaN are absent (flean's own roadmap lists them as
"missing proof areas"). They matter for native x86 code. *Fix:* designed
in from the start but layered (§7.2), so mathematics never sees them.

## 3. Formats and values

```heather
// Only radix 2 (flean dropped radix too; decided in §9).
record Format {
    prec: Nat,                    // significand digits, implicit bit included
    prec_ok: 2 <= prec,
    emin: Int,                    // IEEE's emin and emax: the leading exponents
    emax: Int,
    range_ok: emin <= emax,
    specials: Specials,
}

// What the top binade holds. IEEE interchange formats are `Ieee`; the OCP
// formats pick the others (E4M3 "FN": one NaN pattern, no infinity; E8M0:
// no sign, no zero).
inductive Specials { Ieee, NanOnly, Saturating, UnsignedNoZero }

fn Format::qmin(self F: Format) → Int { F.emin - F.prec.int() + 1 }
fn Format::qmax(self F: Format) → Int { F.emax - F.prec.int() + 1 }
```

The canonical-form condition is a **Boolean function**, so validity is a
proof of `… = True` closed by evaluation for any literal float, and two
finite floats with the same three fields are equal with no proof
comparison:

```heather
fn Format::canonical(self F: Format, mag: Nat, q: Int) → Bool {
    mag < 2 ^ F.prec  &&  F.qmin <= q  &&  q <= F.qmax
        &&  (q == F.qmin  ||  2 ^ (F.prec - 1) <= mag)
}

record Finite(F: Format) { neg: Bool, mag: Nat, q: Int, ok: F.canonical(mag, q) = True }

inductive Float(F: Format) {
    Fin(x: Finite(F)),
    Inf(neg: Bool, has: F.has_inf() = True),
    NaN(has: F.has_nan() = True),
}
```

Evidence-carrying constructors make "this format has no infinity" a type
fact: a match on `Float(e4m3fn)` dismisses `Inf` by evaluation, and no
operation on it can produce one. `binary16`, `binary32`, `binary64`,
`bfloat16`, `e5m2`, `e4m3`, `e3m2`, `e2m3`, `e2m1` and `e8m0` are values
of `Format`. (Parameterised inductives exist in the elaborator's probes;
whether `Float(F)` should be an inductive or a record with a tag is an
implementation detail for round 1.)

The value of a finite float goes through a small exact type:

```heather
record Dyadic { mant: Int, exp: Int }       // mant · 2^exp
fn Dyadic::Same(a, b: Dyadic) → Type        // by shifting to the smaller exponent
fn Dyadic::rat(self d: Dyadic) → Rat
fn Finite::dyadic(self x: Finite(F)) → Dyadic { Dyadic(sign(x.neg, x.mag), x.q) }
fn Finite::val(self x: Finite(F)) → Rat { x.dyadic().rat() }
```

Sums, differences and products of dyadics are dyadics, exactly and
computably; this is the type every operation's exact result lives in before
rounding. Comparing dyadics is comparing `mant₁ · 2^(e₁ - e)` with
`mant₂ · 2^(e₂ - e)` at `e = min(e₁, e₂)`: integer arithmetic, `omega`
territory once the shift is a literal or named. `Dyadic` is also the natural
home for later work (exact interval endpoints, the `Rat`-free fast path for
evaluation).

### 3.1 The value domain in detail

There are three layers, and each theorem lives in the lowest one that can
state it.

**Integers: the representation.** Canonical form, the rounding routine's
branches (shift, quotient, carry, overflow), successor and predecessor, and
the encoding are all facts about `Nat`/`Int` triples. Their proofs are
`omega` and evaluation. Nothing in this layer mentions a fraction.

**`Dyadic`: the exact values.**

- *Carrier.* `Dyadic { mant: Int, exp: Int }`, unnormalised. `Dyadic::Same`
  is `≈`, by aligning to the smaller exponent: `a ≈ b` iff `a.mant ·
  2^(a.exp - e) = b.mant · 2^(b.exp - e)` at `e = min(a.exp, b.exp)`, with
  the shifts as `Nat` powers, so `Int` arithmetic decides it. Normalising
  (odd mantissa, or zero) would make `=` value equality, but every operation
  would then pay for a normalisation and a proof that it normalises. The
  setoid follows the same convention as `Rat` and `CReal` and costs nothing.
  `Finite(F)` is canonical anyway, so normal forms already exist where they
  are wanted.
- *Operations.* `+`, `-`, `*` and `shift(k)` (multiply by `2^k`, which only
  changes the exponent) are exact and computable, and each respects `≈`.
  There is no division. `Dyadic` gets the relation-indexed
  `CommRing(≈, +, *)` instance (`semiring.hthr`) and `Lt`/`Le` by aligned
  `Int` comparison, decidable. It is an ordered commutative ring but not a
  field, and the design does not pretend otherwise.
- *Embedding.* `Dyadic::rat` splits on the exponent's sign: `mant · 2^exp`
  as an `Int` when `exp ≥ 0`, else `Rat(mant, 2^(-exp))`. That needs no
  `Rat::pow` and no `PowOk` evidence, and it evaluates. It is a ring
  embedding that preserves and reflects `≈`, `<` and `<=`; these are the
  only facts that cross into `Rat`.

**Any ordered field `K`: the statements.** `RoundsTo`, the standard model
and every error bound are stated at `K: OrderedField(≈, <, <=, +, *)` from
`ordered_field.hthr`, through `Dyadic::into<K>`. That is
`ofInt(mant) * two^exp`, where `two^exp` uses `K`'s inverse at `2`, and
`0 < 2` supplies the apartness. At `K = Rat` it is `Dyadic::rat` up to `≈`,
and at `K = CReal` it is `CReal::ofRat ∘ Dyadic::rat`. The proof route is
always the same. Prove the fact at `Rat`, where order is decidable and
`RoundsTo` is decidable over the finitely many floats, often by
evaluation for a concrete format. Then **transfer** it along one lemma: an
ordered-ring embedding `Rat → K` that preserves and reflects `<` preserves
`RoundsTo` and every bound whose constants are dyadic. So a generic-`K`
theorem costs one transfer call, not a second proof. Flean's `(R := R)`
annotations disappear because the carrier is read off the argument, as
everywhere in `ordered_field.hthr`.

What is computed where:

| exact value of | carrier | how |
|---|---|---|
| a float | `Dyadic` | `x.dyadic()` |
| `a + b`, `a - b`, `a * b`, `fma(a, b, c)` | `Dyadic` | exact ring operations |
| `a / b`, `sqrt(a)` | `Rat` (not dyadic) | represented for rounding as a dyadic plus sticky, by integer quotient or integer square root |
| a decimal literal, `round_rat(q)` | `Rat` | integer division of `num` by `den` to `prec + 2` bits, with the remainder as sticky |
| `exp(x)`, `log(x)`, any real | `CReal` | §6 |

**Why not a generic carrier throughout (flean's choice).** A generic `R`
gives nothing computable, so flean built ERat and ENNRat beside it. And
because a generic `R` has no integer-level normal form, a comparison of two
powers of two needs `zpow` lemmas instead of `omega`. Here everything below
`K` computes, and only the final statement is generic.

## 4. Equality and order

### 4.1 The relations

- `=` at `Finite(F)` is structural. The only structural difference between
  value-equal finite floats is the sign of zero.
- `≈` at `Finite(F)` designates `x.val ≈ y.val` (equivalently: equal, or
  both zero), and it is decidable. `<` designates the value order and `<=`
  its Bishop dual. `Finite(F)` gets `Equivalence` and `StrictOrder`
  instances, so every `ordered_field.hthr` lemma that needs only a strict
  order applies, and `calc` chains over floats mix freely with `Rat` steps
  through `val`.
- At `Float(F)` there are three more relations, each IEEE-defined and each
  needing its own notation (§4.2):
  - **IEEE comparison**, the quiet predicates of IEEE §5.11: `x <ᵢ y`,
    `x ≤ᵢ y`, `x =ᵢ y`. Every one is false when either side is NaN, and
    `+0 =ᵢ -0`. `=ᵢ` is not reflexive, so it is no `Equivalence`, and it is
    never `≈`. `compare(x, y)` returns `{Lt, Eq, Gt, Unordered}`.
  - **`totalOrder`** (IEEE §5.10): `x ≤ₜ y`, a decidable total order on
    `Float(F)` with `-0 <ₜ +0` and the NaNs at the ends (payload order is a
    bits-level refinement).
  - **Value sameness of non-NaN floats**, `≈` at `Float(F)` restricted to
    the non-NaN values, if a client needs it. Round 1 does not add it.

This settles flean's issue #15 by never overloading: the plain symbol means
the mathematical order, and the two IEEE orders carry a decoration.

### 4.2 Decorated symbols

The lexicon is a curated, context-free table (`crates/syntax/src/lexer.rs`,
`issues/notation-extensibility.md`): a new symbol is a token added there and
then given meaning by a `designation` (`docs/operators-onto-classes-design.md`).
The float library wants one general addition rather than three special
tokens: **a relation symbol immediately followed by one Unicode subscript
letter is a symbol of its own.** So `<ᵢ`, `≤ᵢ`, `=ᵢ` and `≤ₜ`, `<ₜ` are
five names in the symbol namespace, each designated per carrier like `<`.
The rule is the one `·₁₂` already uses, where adjacency plus the subscript
alphabet makes the lexing unambiguous. It also needs `≤` as a Unicode
spelling of `<=`, which the lexer does not have today. The subscript
alphabet is small (`ₐ ₑ ₒ ₓ ₕ ₖ ₗ ₘ ₙ ₚ ₛ ₜ ᵢ ⱼ ᵣ ᵤ ᵥ`) but covers the cases
that matter, and other libraries get the mechanism for free: `≤ₗ` for a
lexicographic order, `≈ₛ` for a second setoid.

That lexer change belongs to the `language` lane, and the lexer is a shared
hotspot, so it is filed as its own issue
([decorated-relation-symbols](../issues/decorated-relation-symbols.md)),
with `math-float` as its customer. The float rounds do not wait for it.
Until it lands they use the named functions (`ieee_lt`, `total_le`), and the
notation is a later designation with no change to any theorem.

## 5. Rounding

### 5.1 The specification is a relation

```heather
inductive Mode { NearestEven, NearestAway, TowardPos, TowardNeg, TowardZero }

// `r` is a correct rounding of the exact value `x` in format `F` under `mode`.
// Stated over any carrier with a strict order and an embedding of Rat,
// so it means the same thing at Rat and at CReal.
fn RoundsTo<K: OrderedField(≈, <, <=, +, *)>(F: Format, mode: Mode, x: K, r: Float(F)) → Type
```

Its clauses are order facts about finitely many floats: for `TowardNeg`, `r`
is finite with `r.val <= x` and every finite `g` with `g.val <= x` has
`g <= r`, or `x` is below the most negative finite and `r` is `-∞` (or the
format's saturation value); nearest modes pick the closer of the two
neighbours with the tie rule; overflow follows IEEE §7.4 per mode and per
`Specials`. Because the floats of a format are a finite, enumerable set,
"every `g`" quantifies over a finite set, and at `Rat` the relation is
decidable.

The laws flean spread over classes are theorems about the relation, proved
by cases on `mode`: uniqueness (the relation is functional modulo `≈`),
monotonicity, idempotence on representable values, `round(-x) =
-round'(x)` with the conjugate mode, bracketing (`TowardNeg ≤ nearest ≤
TowardPos`), grid preservation, and the error bounds of §5.3.

### 5.2 One executable rounding

```heather
// Round `d`, or a value strictly between `d` and the next dyadic at
// `d.exp` when `sticky`, to format F.
fn round(F: Format, mode: Mode := NearestEven, neg: Bool, d: Dyadic, sticky: Bool) → Float(F)

theorem round::correct(…): RoundsTo(F, mode, exact, round(F, mode, neg, d, sticky))
```

This is flean's `roundIntSigM` with the hooks replaced by a `match` on the
mode, and with the validity proof moved out of the definition: the result
is built through a smart constructor whose canonical-form obligation is a
named lemma about the shift, not 60 lines inlined in the function body.
`Rat` rounding (`round_rat`) is a thin wrapper: write the rational as
`n / d`, take enough quotient bits by integer division, and the remainder
gives the sticky flag.

### 5.3 Error bounds

The theorem everything downstream cites is Higham's **standard model**:
for a rounding `r` of `x` in the normal range, `r.val = x·(1 + δ)` with
`|δ| ≤ u`, where `u = 2^-prec` for nearest modes and `2^(1-prec)` for
directed ones; in the subnormal range the error is absolute, at most half
(or one) `2^qmin`. Both are stated with `AbsLt`/`AbsLe` predicates from
`ordered_field.hthr` so they hold at any `OrderedField`, and proved once at
`Rat`. The γ-notation composition (`γ_n = n·u / (1 - n·u)`) is the next
layer and is what summation and dot-product bounds use.

### 5.4 Generic roundings

Some results hold for any rounding that is monotone, idempotent on the
grid and faithful (the result is one of the two neighbours): Sterbenz,
Fast2Sum's exactness under faithful rounding, stochastic-rounding bounds
for ML, round-to-odd for double-rounding proofs. For those a record

```heather
record Rounding(F: Format) { rel: Rat → Float(F) → Type, faithful: …, monotone: … }
```

with `Mode::rounding(F, mode)` as the IEEE instances. Most of the library
never sees it.

**Stochastic rounding** (ML, later) is the one mode that is not a function
even on `Rat`: it is a distribution over the two neighbours. In the set
reading of §5.5 it is not odd at all. Its support is the faithful set, so
every bound that holds for faithful rounding holds for each outcome
pointwise, and the expectation bounds that make it attractive need
probability theory, which comes with the ML milestones. Until then the
`Mode` enum stays the five IEEE modes (Minus, 2026-10-20: practical, and
what people use). Round-to-odd joins as an internal mode for
double-rounding proofs when a round needs it.

### 5.5 Syntax

Two things need spelling: the **relation** ("`r` is a correct rounding of
`x`"), which makes sense at any carrier, and the **function** ("compute the
rounding of `x`"), which exists only at `Dyadic` and `Rat`. The proposal
reads the rounding of `x` as the *set* of its correct roundings, so a single
notation serves both:

```heather
○x                  // the set of correct roundings of x: a predicate on Float(F)
r ∈ ○x              // RoundsTo(F, NearestEven, x, r), at any ordered field
r ∈ ○[TowardZero] x // the same under another mode
r ∈ ▽x,  r ∈ △x     // round down / round up: the two directed modes interval proofs use
r ∈ ○ᶠx             // faithful: r is one of the two neighbours of x

round(x)            // the function, at Dyadic and Rat; F from the expected type,
                    // mode a default argument (named-arguments-design §9.6)
round(x, mode := TowardPos)
round::mem(x): round(x) ∈ ○x        // the bridge theorem
```

Reasons for this shape:

- For the IEEE modes `○x` is a singleton up to `≈`
  (`RoundsTo::unique`), so `r ∈ ○x` reads as "`r` is the rounding". For a
  faithful rounding it has two elements, and for stochastic rounding it is
  the support. One notation covers the deterministic and non-deterministic
  cases, which is what a constructive treatment of the reals needs (§6): a
  real has a computable faithful rounding but only a set-valued correct
  rounding until apartness is supplied.
- `○` (U+25CB, white circle) is the handbook's and flean's symbol for
  "rounded", so it reads naturally to anyone coming from either. `▽`/`△`
  match the handbook's RD/RU and interval-arithmetic usage.
- The format is read from the type of `r`, the expected type, as for
  carrier-directed numerals. Where nothing pins it, `○[binary32] x` names
  it.
- The standard model reads as written in the literature:
  `r ∈ ○x → ∃ δ, AbsLe(δ, u(F)) ∧ r.val ≈ x * (1 + δ)` for `x` in the
  normal range.

`○`, `▽` and `△` are prefix tokens and `∈` an infix one (it also has uses
outside floats), so they are part of the same language-lane issue as §4.2.
Until it lands the spellings are `x.RoundsTo(F, mode, r)`, `round(…)` and
`round::correct`.

## 6. The reals, constructively

Rounding a real number to a float is not a computable function: at a
breakpoint (a representable value for directed modes, a midpoint for
nearest modes) no finite approximation decides which side the real is on.
Flean hides this behind `LinearOrder ℝ` and `Int.log`. Heather states it
the way `CReal`'s inverse does, by asking for the evidence that makes it
computable:

- **The relation is always available.** `RoundsTo(F, mode, x, r)` is
  meaningful for `x : CReal` and transfers along `CReal::ofRat`, so every
  operation's correctness theorem (exact value is a dyadic) holds at
  `CReal` as a corollary with no new proof.
- **Correct rounding computes from apartness.** `round_real(F, mode, x,
  apart: x.Apart(breakpoints of F))` refines `x` until its interval misses
  every breakpoint, which the apartness proof bounds. This is exactly the
  shape of flean's `exp`/`log` termination proofs: the Padé gap *is* an
  apartness proof from the breakpoints, so correctly rounded transcendental
  functions become `round_real` of a `CReal` plus that proof.
- **Faithful rounding computes always.** Approximating `x` strictly within
  half the smallest gap (`2^qmin / 2`) and rounding the approximation to
  nearest gives one of the two floats around `x`: the approximation can
  overshoot a neighbour by less than half of any gap, so it is still nearer
  that neighbour than the next one out. That is a faithful rounding with no
  side condition. This is the
  honest constructive answer for "round this real", and it is enough for
  every error bound stated with `u` doubled.

No classical axiom appears anywhere, and nothing returns a junk value.

**Classical users get the same theorems, not a second profile** (Minus,
2026-10-20). The constraint the correct-rounding statements actually need is
weaker than apartness. It is that `x` is *placed* relative to each
breakpoint: `x < b ∨ x ≈ b ∨ b < x`, for the finitely many breakpoints of
`F` near `x`. Call it `F.Placed(x)`. Apartness from the breakpoints implies
it constructively. Excluded middle implies it for every `x`. So the theorem
is stated once:

```heather
theorem RoundsTo::exists(F, mode, x: K, placed: F.Placed(x) := infer): ∃ r, r ∈ ○[mode] x
```

A constructive caller supplies `placed` from an apartness proof or from a
decision at `Rat`. A classical caller works under an assumption scope
(`issues/implicit-logical-assumptions.md`) whose provider derives `Placed`
from excluded middle, and the parameter is discharged by `infer` without
being written: the constraint dissolves. The difference shows only in
computation. Under the classical provider the witness is opaque and does not
evaluate, which is exactly the boundary that issue draws between logical
evidence and `Decide`. Rounds 1–5 never need it: every exact value they
round is a dyadic or a rational, whose placement is decided. It is recorded
for the reals submilestone.

## 7. Operations, bits and the machine

### 7.1 Operations

Add, sub, mul and fma compute the exact dyadic and call `round`; div and
sqrt compute an integer quotient (or integer square root) with enough extra
bits and pass the remainder as the sticky flag. Each operation has:

- a value theorem: `RoundsTo(F, mode, a.val ∘ b.val, a ∘ b)` for finite
  inputs, no side condition (P9);
- a sign-of-zero theorem (IEEE §6.3);
- a special-value table (NaN, infinities), proved by evaluation over the
  constructor cases.

Format conversion is `round` applied to the source's dyadic, so widening is
exact by a theorem and narrowing (to the storage formats) is correctly
rounded by the same theorem; flean's separate `fromFp_val_eq_round` and
the `NarrowingContext`/`WideContext` machinery disappear.

### 7.2 Bits, payloads and flags

- **Encoding** is one pair `encode: Float(F) → BitVec(F.width())`,
  `decode` back, with width, bias and field positions computed from the
  `Format`, and the round trip proved once for every `Format` with a
  standard layout. It uses `lib/std/bitvec.hthr`, so the native lane can
  use the same definitions.
- **NaN payloads** live at the bits layer, not in `Float(F)`: the semantic
  `NaN` is one value, and a *platform policy* (a record) says which bit
  pattern an operation produces from which input patterns. x86 SSE's
  rules (default QNaN, propagate the first NaN operand quietened) are one
  instance.
- **Exception flags** are a separate output: `op_flags(F, mode, a, b) →
  Flags` with invalid, divide-by-zero, overflow, underflow (with the
  before/after-rounding tininess choice as a parameter) and inexact. Pure
  mathematics uses the result alone.

### 7.3 Native code (later, in its own lane)

Once the bits layer exists, the native lane (`heather-in-heather`) can
state SSE instructions as "the result bits are `encode(op(decode(a),
decode(b)))` under the policy", which is what lets compiled floating-point
code carry certificates. That work touches `lib/std/arch/` and the native
support lists and is out of scope here.

## 8. Rounds and submilestones

One PR per round. Each lands its own modules under a new `lib/std/float/`
directory (the mathematics lane), and none touches the shared hotspots.
`math-float` is done when rounds 1–5 have landed (Minus, 2026-10-20). The
later work is submilestones of it that do not block it. The ids are the
roadmap's.

| round | submilestone | content |
|---|---|---|
| 1 | `float-values` | `Format`, the standard formats as values, `Finite(F)`, `Float(F)`, `Dyadic` with its ring and order, `val`, `≈`/`<` with `StrictOrder`, successor and predecessor, and the literal constants (`max_finite`, `min_normal`, `min_subnormal`) proved canonical by evaluation. |
| 2 | `float-rounding` | `RoundsTo`, `round` on dyadics with sticky, `round_rat`, `round::correct`, uniqueness, the mode laws, and the transfer lemma to any `OrderedField`. |
| 3 | `float-error` | The standard model, absolute subnormal bounds, `ulp`, γ-composition. |
| 4 | `float-arith` | Add/sub/mul/fma with value, zero-sign and special-value theorems; then div and sqrt by sticky quotients; format conversion. |
| 5 | `float-eft` | Sterbenz, Fast2Sum, TwoSum, TwoProduct (by fma), Veltkamp; then Kahan summation. |
| later | `float-bits` | Encode/decode and the round trip, the OCP storage formats, NaN payload policies and flags. |
| later | `float-reals` | Transfer to `CReal`, faithful rounding, `round_real` with apartness, `Placed`. |
| later | `float-transcendental` | Correctly rounded `exp`/`log`: a `CReal` series plus a Padé apartness proof. |

ML numerics on top (dot products, softmax, stochastic rounding) belong to
the ML milestones that pull them, not here. The notation of §4.2 and §5.5
arrives through
[decorated-relation-symbols](../issues/decorated-relation-symbols.md) in
the language lane, whenever that lands. No round waits for it.

Tactics, per the project principle: rounds 2–4 will repeat "shift to a
common exponent and compare integers", and the error-analysis rounds will
repeat "multiply out `(1 + δᵢ)` and bound". Each gets a `tactics` issue the
third time it is written by hand, naming `math-float` as its customer.
Flean's `linearize` and `bound_calc` are evidence of what those tactics need
to do.

## 9. Decisions and what is still open

Minus's answers to the first draft (2026-10-20):

1. **Value carrier:** dyadics embedded in `Rat`, with generic `OrderedField`
   statements only where `CReal` needs them. Agreed. Minus asked for more
   detail, which is now §3.1.
2. **Exponent:** store the quantum exponent. Agreed.
3. **Rounding mode:** an enum argument. Agreed, "not one hundred percent a
   fan but practically that's what people use". Stochastic rounding is
   deferred, and §5.4 records how it fits the set reading.
4. **One `Format` record** for IEEE and OCP storage formats. Agreed.
5. **NaN payloads and flags** at the bits layer, behind a platform policy.
   Agreed.
6. **Binary only.** Agreed.
7. **Classical users:** no separate profile. Constraints that dissolve under
   classical assumptions, with the same theorems (§6, `Placed`). Not urgent.
8. **Orders:** the IEEE orders get special notation. §4.2 proposes
   subscript-decorated relation symbols.
9. **Scope:** `math-float` is rounds 1–5, and the rest are submilestones
   (§8).

Still open, for review on this design:

- **The rounding notation of §5.5**, Minus asked for syntax. The proposal
  is `○x` as the set of correct roundings, `r ∈ ○x` the relation,
  `round(x)` the function, and `▽`/`△`/`○ᶠ` the directed and faithful
  variants.
- **The decoration letters of §4.2**: `ᵢ` for the IEEE quiet comparisons
  and `ₜ` for totalOrder.
- **Whether `Float(F)` is a parameterised inductive or a record with a
  tag.** This is a round-1 implementation detail. It decides only how the
  evidence-carrying `Inf`/`NaN` constructors are spelled.
