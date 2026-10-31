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

As landed in round 1 (`lib/std/num/float/float.hthr`; §10 records what changed
from the first sketch):

```heather
// What the format keeps for special values. E4M3 is `NanOnly`: no infinity,
// and its all-ones pattern is NaN. The OCP FP6/FP4 formats are `FiniteOnly`.
// E8M0 is a scale with no significand or zero, so it is not a `Format`.
inductive Specials { Ieee, NanOnly, FiniteOnly }

// Only radix 2. `frac` fraction bits (precision `frac + 1`), `emin` IEEE's
// least normal exponent, `span` binades above it (IEEE's emax is
// `emin + span`).
record Format { frac: Nat, frac_ok: 1 <= frac, emin: Int, span: Nat, specials: Specials }

fn Format::qmin(self F: Format) → Int { F.emin - F.frac.int() }  // subnormals are multiples of 2^qmin
fn Format::half(self F: Format) → Nat { Nat::pow(2, F.frac) }      // least normal significand
fn Format::top(self F: Format) → Nat { Nat::pow(2, F.prec()) }     // = half · 2, by computation
```

The canonical-form condition is a **Boolean function** of naturals only.
Validity is an `IsTrue` proof, which closes by `trivial` for any literal
float. `IsTrue` proofs are unique, so two finite floats with the same three
parts are equal (`Finite::ext`):

```heather
fn Format::canonical(self F: Format, mag, bexp: Nat) → Bool  // fits, in range, normal above bexp 0, not the NaN pattern

record Finite(F: Format) { neg: Bool, mag: Nat, bexp: Nat, ok: F.canonical(mag, bexp).IsTrue() }
fn Finite::q({F: Format}, self x: Finite(F)) → Int { F.qmin() + x.bexp.int() }   // the quantum exponent

inductive Float(F: Format) {
    Fin(x: Finite(F)),
    Inf(neg: Bool, has: F.specials.has_inf().IsTrue()),
    NaN(has: F.specials.has_nan().IsTrue()),
}
```

Evidence-carrying constructors make "this format has no infinity" a type
fact: a match on `Float(e4m3())` dismisses `Inf` by evaluation
(`Float::not_inf`), and no operation on it can produce one. `binary16`, `binary32`, `binary64`,
`bfloat16`, `e5m2`, `e4m3`, `e3m2`, `e2m3`, `e2m1` and `e8m0` are values
of `Format`.

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
  is `≈`, defined through the embedding: `a ≈ b` iff `a.rat() ≈ b.rat()`,
  which unfolds to one `Int` equation between cross products of powers of
  two, so `Int` arithmetic decides it. The aligned form ("shift both
  mantissas to the smaller exponent") is a theorem, `Dyadic::align`, not the
  definition. Normalising
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
- *Embedding.* `Dyadic::rat` splits the exponent into its positive and
  negative halves, `Rat(mant · 2^e⁺, 2^e⁻)` with `e = e⁺ - e⁻`
  (`Int::pos_part`, `Int::neg_part`). That needs no case on the sign, no
  `Rat::pow` and no `PowOk` evidence, and it evaluates. `Dyadic::rat_split`
  says that any split `e = p - q` gives the same rational, and every
  homomorphism proof goes through it, because `omega` reasons about the
  natural halves but not about `toNat`. It is a ring
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
  standard layout. It uses `lib/std/bitvec/bitvec.hthr`, so the native lane can
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

One PR per round. Each lands its own modules under a new `lib/std/float/` (now `lib/std/num/float/`)
directory (the mathematics lane), and none touches the shared hotspots.
`math-float` is done when rounds 1–5 have landed (Minus, 2026-10-20). The
later work is submilestones of it that do not block it. The ids are the
roadmap's.

| round | submilestone | content |
|---|---|---|
| 1 | `float-values` | `Format`, the standard formats as values, `Finite(F)`, `Float(F)`, `Dyadic` with its ring and order, `val`, `≈`/`<` with `StrictOrder`, and the constants (`zero`, `min_subnormal`, `min_normal`, `max_finite`) canonical for every format. Landed; §10. |
| 2 | `float-rounding` | Successor and predecessor with their spacing, `RoundsTo`, `round` on dyadics with sticky, `round_rat`, `round::correct`, uniqueness, the mode laws. Part A (the relation, the executable rounding and its correctness in every mode, sign symmetry) landed, §11; part B (successor/predecessor with spacing, uniqueness, bracketing, monotonicity, idempotence) landed, §12. The transfer lemma to any `OrderedField` moved to `float-reals`, its only customer. |
| 3 | `float-error` | The standard model, absolute subnormal bounds, `ulp`, γ-composition. Landed; §13. |
| 4 | `float-arith` | Add/sub/mul/fma with value, zero-sign and special-value theorems; then div and sqrt by sticky quotients; format conversion. Landed, §14; sqrt §14.1. |
| 5 | `float-eft` | Sterbenz, Fast2Sum, TwoSum, TwoProduct (by fma), Veltkamp; then Kahan summation. |
| later | `float-bits` | Encode/decode and the round trip, the OCP storage formats, NaN payload policies and flags. |
| later | `float-reals` | Transfer to `CReal`, faithful rounding, `round_real` with apartness, `Placed`. Started: `RoundsToReal` and Ziv's search with fuel ([creal-transcendental-round.md](creal-transcendental-round.md)); termination is [float-round-real-termination](../issues/float-round-real-termination.md). |
| later | `float-transcendental` | Correctly rounded `exp`/`log`: a `CReal` series plus a Padé apartness proof. Started: `exp_fin`/`log_fin` at finite floats, binary32 by evaluation ([creal-transcendental-round.md](creal-transcendental-round.md)); `Float::exp`/`Float::log` over every float with the §9.2 specials. |

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

## 10. Round 1 as landed (`float-values`)

Modules: `lib/std/num/float/dyadic.hthr` and `lib/std/num/float/float.hthr`, with
three general facts added to their home files: `Nat::pow_pos` (an evidence
rule, so `Rat(n, Nat::pow(2, k))` finds its denominator's positivity) and
`Nat::le_pow_self` in `nat.hthr`, and `Nat::int_pow_add` and
`Int::pos_part`/`neg_part`/`pos_sub_neg` in `int.hthr`. Tests are in
`lib/_tests/std/num/float/float_tests.hthr`, the refusals in
`crates/elab/tests/lib_std_float.rs`.

What changed from the sketch in §3, and why:

- **`Float(F)` is an inductive with a value parameter.** Round 1 first
  wrote it as a generic `Extended<Finite(F), I, N>` applied to the format's
  evidence types, because surface inductives did not take value parameters
  (`docs/surface-value-parameters.md` §6). That was the one design oddity
  Minus flagged, and value parameters on `inductive` landed in PR #89, so
  `Float(F)` is now declared directly. Its methods live on `Float`
  (`x.is_inf()`, `x.not_inf(refl)`), which a type-valued function could not
  give: a method call on an `Extended` application did not resolve the
  `Float::` members.
- **The exponent is stored biased, `bexp: Nat`, with `q = qmin + bexp`.**
  It is still the quantum exponent (§9, decision 2), offset from the
  format's least one, so the canonical-form condition involves only
  naturals: `omega` does not reason about `Int::toNat`, and the condition
  never needs it.
- **Precision is `frac` fraction bits** (precision `frac + 1`), so `2^prec`
  is `2^frac · 2` by computation and nothing takes a power of a truncated
  subtraction. The exponent range is `emin` plus `span` binades, so
  `emin <= emax` needs no proof field.
- **`Specials` is `Ieee`, `NanOnly` and `FiniteOnly`.** Saturation is a
  conversion policy rather than a property of a format, and it belongs to
  the arithmetic rounds. E8M0 has no significand and no zero, so it is not a
  `Format`. It will be a separate scale type when the microscaling block
  formats are needed.
- **The constants are generic**, each built through
  `Format::canonical_intro` from facts about naturals. The sketch had them
  only for literal formats, but round 2 needs `max_finite(F)` for overflow at
  every `F`.
- **Successor and predecessor moved to round 2**, because the rounding
  spec is what states and uses their spacing.

Observations for later rounds:

- `omega` treats `Nat` subtraction as an atom, so `max_finite` feeds it
  `Nat::sub_add_cancel` facts. Projections of a constructor application
  (`Rat(a, b).num`) are atoms to `omega` and `ring` as well; a typed `let`
  that states the unfolded cross-product equation works around that.
- When a `Dyadic`, `Finite` or `Rat` relation unfolds into another
  carrier's, the implicit arguments of that carrier's lemmas are mis-inferred
  (the kernel then refuses the term), so the module passes them by name
  (`Rat::same_sym(x := a.rat(), y := b.rat(), h := h)`). If this recurs in
  round 2 it is a language issue worth filing.
- `Dyadic::rat_add` is the costliest item in the module (a `ring` call over
  large atoms) but well inside the rails.

## 11. Round 2 as landed, part A (`float-rounding`)

Module: `lib/std/num/float/round.hthr`, with general facts added to their home
files: `Nat::shr` and its floor bounds, `pow_le_pow_r`,
`lt_of_mul_lt_mul_r` and the parity steps in `nat.hthr`; the midpoint and
subtraction-order lemmas in `rat.hthr`; `Option::none_ne_some` in
`option.hthr`; `Dyadic::le_of_mant_le` and its converses in `dyadic.hthr`;
`Specials::inf_free`, `Format::canonical_elim`, `Format::max_mag_bounds`
and `Float::neg` (prefix `-`) in `float.hthr`. Tests are in
`lib/_tests/std/num/float/round_tests.hthr`, the refusals in
`crates/elab/tests/lib_std_float.rs`.

**The relation.** `RoundsTo(F, mode, x, r)` is stated at `Rat` by cases on
the result and the mode. A finite result is the greatest float at or below
`x` (`Finite::Below`), the least at or above (`Finite::Above`), or a
nearest one (`Finite::Nearest`, no float closer) with the tie rule:
`NearestEven` says every other nearest float has the same value or the
result's significand is even, `NearestAway` that every nearest float is no
larger in magnitude. Overflow follows IEEE §7.4: a nearest mode returns
infinity from the threshold `(2^(prec+1) - 1) · 2^(qmax - 1)` on
(`Format::ovf`) and a finite nearest result carries `Fits` (below the
threshold, when the format has infinities); a directed mode returns
infinity only past every finite float (`Exceeds`/`Undercuts`). A format
without infinities saturates: a directed rounding past the largest float
is the largest float, as `TowardPos`'s second disjunct says.

**The computation goes through half-units.** Every finite float is a whole
number of half-units `2^(qmin - 1)` (`Finite::H`, `Format::grid`), so an
exact nonnegative value is described to the rounding by `h`, its magnitude
in half-units rounded down, and a sticky bit (`Format::Approx`). Every
float-against-`x` comparison is then an integer comparison
(`Format::le_cut`, `ge_cut`), which is what makes the proofs `omega`-sized.
The neighbours come from `h` alone: the exponent is the least `e <= span`
at which `h` shifted right by `e + 1` fits the significand
(`Format::e_of`, a bounded search that starts at the least exponent, so a
result above it is normal), the cell's float is `(h >> (e+1), e)`
(`Format::down`), and the step up is one significand higher, carried into
the next binade at the top of one, or none past the largest float
(`Format::up`, characterised by `UpIs`/`UpCases`). The midpoint test
compares `h`'s offset into the cell with `2^e` and, on equality, the
sticky bit. Half-units rather than units are what let the midpoint of a
subnormal cell be a grid point.

**API, and how it differs from §5.2.** `Format::round_h(mode, h, st)` is the
sticky-aware primitive the arithmetic rounds will call: they compute their
exact result at half-unit resolution with a sticky bit. `round_signed` adds
the sign, rounding the magnitude under the conjugate mode
(`Mode::conj`) and negating. `Format::round_dyadic(mode, d)` rounds an exact
dyadic by shifting, and `Format::round_rat(mode, x)` rounds a rational by
integer division with the remainder as sticky. Their theorems are
`round_h_correct`, `round_signed_correct`, `round_dyadic_correct` and
`round_rat_correct`, all for every mode; §5.2's single `round(F, mode, neg,
d, sticky)` was not kept, because a sticky bit at a dyadic's own exponent
does not locate a value at half-unit resolution when that exponent is
coarser than the grid. Sign symmetry is `Format::rounds_neg`:
`RoundsTo(F, mode.conj(), -x, r) → RoundsTo(F, mode, x, -r)`. An exact zero
rounds to `+0`; a negative value that rounds to zero gives `-0`.

**Cost.** `round_rat` evaluates through `Nat::divmod`, whose cost is linear
in the quotient, so literal `round_rat` tests stay on E2M1-sized values;
`round_dyadic` and `round_h` evaluate through the kernel's accelerated
`half`, `leb` and `le_dec`, so E5M2 and E4M3 overflow cases compute by
`refl`. A decision that uses `Nat::eq_dec` is not accelerated and ran out of
fuel at E5M2's magnitudes; the module tests equality as `¬(n + 1 <= m)`
instead. A binary division for `round_rat` is
[float-round-rat-division-cost](../issues/float-round-rat-division-cost.md).

Observations for later rounds:

- `omega` splits a conjunction hypothesis only one level deep, and it
  reflects every arithmetic hypothesis in scope, `Rat` relations included
  (they unfold to cross-multiplied `Int` facts). The midpoint proof first
  checked in about a minute with every fact in one context; split into
  small lemmas whose contexts hold only the integers it needs, and with the
  arithmetic facts bound one per `let`, it checks in seconds.
- `omega` does not reason about truncated `Nat` subtraction, so every use
  feeds it a `Nat::sub_add_cancel` fact, as round 1 found.
- Dependent definitions (the step up depends on proofs from the search) are
  written as helper functions that take the decision as an argument
  (`down_at`, `up_at`, `up_in`), so a proof can match on the same decision
  with a short motive.
- The transfer lemma to an `OrderedField` has no customer before
  `float-reals`, so it moved there.

## 12. Round 2 as landed, part B (`float-rounding`)

Same module, `lib/std/num/float/round.hthr`; new general facts went home too:
`Nat::not_even_succ_of_even` in `nat.hthr`, and the distance-to-midpoint
lemmas (`mid_le_of_dist`, `le_mid_of_dist`, `le_of_double_le` and their
subtraction forms) in `rat.hthr`.

**Uniqueness.** `Format::rounds_unique` says two correct roundings of one
value in one mode are `Float::Same`: finite with equal values (so `+0` and
`-0` agree), or the same infinity. The directed modes are unique from the
relation alone (`Below`/`Above` are extremal; a saturated result and an
infinity exclude each other through `has_inf`). The nearest modes need more
than the relation states, because "every other nearest float" could in
principle include a third float. It comes from the computation:
two nearest floats to a nonnegative value are either equal in value or
exactly the cell's float and its step up (`Format::near_split`), and those
two have significands of different parity (`UpIs.odd`, the converse of
`UpIs.even`). Two canonical floats with equal values have equal fields
(`Format::canon_eq`, `Finite::parts_of_same`), so parity is a property of
the value. Negative values flip to positive with `nearest_flip`. Two
corollaries: `rounds_is_round_rat` (every correct rounding is the
executable one) and `rounds_exact`/`round_rat_exact` (a representable value
rounds to itself in every mode).

**Neighbours.** `Finite::next_up(f)` is the least float strictly above `f`,
`None` above the largest; `next_down` is it through negation. Above a
nonnegative float it is the cell's step up from the float's own half-unit
count; above a negative one it is the greatest float strictly below the
magnitude, negated; both zeros step to the least positive subnormal. The
specifications are `Finite::IsNextUp`/`IsNextDown` (strictly beyond, and
least/greatest among those beyond), proved by `next_up_spec` and
`next_down_spec`. Spacing is `next_up_spacing`: above a nonnegative float
the next is `2^(bexp + 1)` half-units further, one quantum `2^(bexp +
qmin)` in value (`next_up_gap`), across binade boundaries included because
the carry keeps the lower float's exponent.

**Mode laws.** `Float::Le` extends the value order by `-∞` least and `+∞`
greatest, with NaN unrelated. Every finite correct rounding is one of the
value's two neighbours (`rounds_faithful`), so

- bracketing: `rounds_ge_down` and `rounds_le_up` put a correct rounding in
  any mode between the roundings toward `-∞` and toward `+∞`;
- monotonicity: `rounds_mono` (and `round_rat_mono` for the executable
  rounding) say `x <= y` never rounds lower. The only case the neighbour
  argument leaves is the lower value rounding up past where the higher one
  rounds down; each directed mode excludes it directly, `TowardZero`
  through the zero float, and in a nearest mode it forces the two values to
  be one tie (`near_cross`), where uniqueness finishes it. That needs
  `rounds_respects` (a correct rounding depends on the value up to `≈`).
- `rounds_exact` above is idempotence.

Observations:

- `omega` sees a `Rat` `≈` fact as a cross-multiplied equation between
  opaque atoms, so a distance fact like `f.dist(x) ≈ x - f.val()` does not
  connect to `f.val() < g.val()`; the order lemmas on subtraction
  (`le_of_sub_le_sub_l`) do it in one step.
- `Float::Le(Float::Fin(f), Float::Inf(…))` could not infer `Float`'s format
  from the field, and the library named it (`Float::Le(F := F, a := …, b :=
  …)`) until
  [value-param-constructor-implicit-inference](../issues/value-param-constructor-implicit-inference.md)
  (closed 2026-10-21) read it off the fields; the plain spelling is used now.

## 13. Round 3 as landed (`float-error`)

One module, `lib/std/num/float/error.hthr`, over round 2's internals. Two
general facts went home: `Rat::le_div_of_mul_le` and `Rat::rel_of_abs_le`
(an absolute bound `|y - x| <= u·|x|` at a nonzero `x` as a relative error
`y ≈ x·(1 + e)`, `|e| <= u`) in `rat.hthr`, and the evidence rules
`Format::half_pos`/`Format::top_pos` in `float.hthr`.

**One picture.** A nonnegative value `x` lies in the cell of the greatest
float at or below it, `d = F.down(F.rat_h(x))`. The cell is `2^(d.bexp + 1)`
half-units wide, one ulp of `d`, and its other end is `d`'s step up (or the
cell has none and `d` is the largest float). Every finite correct rounding
is one of the two ends (`rounds_faithful`), so it is within a cell width of
`x` (`nbr_err`), and a nearest one within half of it (`nearest_err`).
Negative values round `-x` under the conjugate mode (`rounds_flip`). The
module never re-derives anything about rounding: every bound is a property
of where the cell is.

**Ulps and errors.** `Format::ulp_at(x)` is the ulp of the cell's float and
`Format::err_at(mode, x)` the error a mode allows there, as a power of two
in half-units (`Mode::err_exp`: half an ulp for the nearest modes, one for
the directed ones). Both compute on literal formats. The headline is
`Format::rounding_error`: for `|x| <= max_finite`, a correct finite rounding
`r` has `|r - x| <= err_at(mode, x)`; `err_le_ulp` and `err_half_ulp` relate
it to the ulp.

**The standard model.** `u = 1 / u_den` with `u_den` the format's `top`
(`2^prec`) for the nearest modes and `half` for the directed ones, so `u` is
`2^-prec` or `2^(1-prec)`, as §5.3 says. In the normal range the cell's
float has a full significand, so `err_at <= u·|x|` (`relative_error`), and
`standard_model` states it Higham's way: `∃ e, |e| <= u ∧ r ≈ x·(1 + e)`. In
the subnormal range `d.bexp` is zero and the error is the absolute `η`
(`Format::eta`, half or one `2^qmin`; `subnormal_error`). `error_bound`
combines them: `|r - x| <= u·|x| + η` everywhere in range.

**γ.** `Format::gamma(mode, n) = n / (u_den - n)`, which is `n·u / (1 -
n·u)` cleared of its fraction; it is meaningful for `n < u_den`, and
`gamma_at` reads it as `n / D` when `u_den = D + n`. The algebra is
`gamma_add` (`γm + γn + γm·γn <= γ(m + n)`), `gamma_mono`, `u_le_gamma` and
`theta_mul` (`|a| <= γm`, `|b| <= γn` give `|(1 + a)(1 + b) - 1| <= γ(m +
n)`). Composition is over lists: `List::prod_one_add(ds)` is `∏(1 + dᵢ)`,
`List::AllAbsLe(ds, u)` the hypotheses, and `gamma_prod` concludes
`|∏(1 + dᵢ) - 1| <= γ(len ds)` for `len ds < u_den`. The bounds are stated
at `Rat` with `abs`; the transfer to an arbitrary ordered field stays in
`float-reals` with the rest of the transfer.

Not in this round, filed or left for the customer that pulls them: the
bound relative to the result (`|r - x| <= u·|r|`), bounds for the overflow
band between `max_finite` and the overflow threshold in the nearest modes,
and inverse factors `(1 + δ)⁻¹` inside a γ product (Higham's `ρ = ±1`).

Observations:

- `omega` does not split a conjunction hypothesis it is handed; binding
  `.left` and `.right` as separate `let`s does. Large integer contexts are
  slow for it, so the cell facts are small lemmas (`up_H`, `top_H`) rather
  than one omega call.
- `ring` with hint equations fails once the cross-multiplied degree is high
  (γ's algebra has three denominators). The robust form states the
  inequality's Int cross-multiplication explicitly, which converts to
  `Rat::Le` definitionally, and proves it with hint-free `ring` plus `omega`
  over nonnegative Nat casts (`gamma_add_core`).
- A record field's `Pos` default ran in the record's module, so a default
  citing an evidence rule from a module the record's module cannot see
  (`Rat(1, F.top())` with `top_pos` in `float.hthr`) failed. Rule citation
  now resolves the rule's own qualified name when the module being
  elaborated imports it (test `a_field_default_cites_a_rule_its_record_module_cannot_see`).
- A non-ASCII character in source (an attempted `δ` identifier) was reported
  as a byte and the snippet renderer panicked on the split character; both
  are fixed.
- `[d1, d2].prod_one_add()` is refused ("unbound name"): a list literal has
  no carrier for method lookup until it is checked against a type, the same
  gap as [list-literal-left-of-append](../issues/list-literal-left-of-append.md).
  The tests write `List::prod_one_add([d1, d2])`.

## 14. Round 4 as landed (`float-arith`)

Module: `lib/std/num/float/arith.hthr`. General facts went home: binary long
division `Nat::ldiv` with `ldiv_div`/`ldiv_mod` in `nat.hthr`; the sign rules
for products and reciprocals (`Rat::mul_nonpos_l`/`_r`,
`mul_nonneg_of_nonpos`, `recip_nonneg`/`nonpos`) in `rat.hthr`;
`Dyadic::mant_zero` and `Dyadic::sign_or` in `dyadic.hthr`;
`Specials::nan_of_inf` in `float.hthr`; and the rounding-side pieces in
`round.hthr` (below). Tests are in
`lib/_tests/std/num/float/arith_tests.hthr`, the refusals in
`crates/elab/tests/lib_std_float.rs`.

**One signed rounding.** Every operation computes a sign bit, a magnitude in
half-units and a sticky bit, and calls `Format::round_signed` once. The sign
theorem is then one lemma for every operation: `round_signed_sign` says the
result carries the sign it was given (`Float::SignIs`), because a rounding of
a magnitude is never negative (`round_h_sign`, by cases through the
rounding's branches, with `up_pos` for the step up). That is what makes an
inexact result that rounds to zero keep the exact value's sign, and an
overflow's infinity carry it, as IEEE 754 §6.3 asks, without a case in any
operation.

- Add, sub, mul and fma have an exact `Dyadic` and round it with
  `Format::round_exact(mode, d, z)`: the dyadic's sign, or `z` when it is
  zero (`Dyadic::sign_or`). The operation passes §6.3's zero sign as `z`:
  `Mode::sum_zero_neg` for a sum (the operands' sign when they agree,
  otherwise `+0`, `-0` toward `-∞`), the exclusive or for a product, and the
  sum's rule with the product signed as a product for fma. An exact zero
  rounds to exactly `Finite::zero(F, z)` (`round_exact_zero`, from
  uniqueness and the sign, since a value-zero float with a given sign is that
  zero: `Finite::zero_of_val`). `round_exact` differs from `round_dyadic`
  only at zero, where `round_dyadic` gives `+0`.
- Sub is `a + (-b)`, so `x - x` is `+0` except toward `-∞`
  (`Finite::sub_self`) whatever `x`'s sign.
- Div has no exact dyadic: the quotient is the rational `a.quot(b) =
  a.val() · b.val()⁻¹` (`Rat::recip`, total), its magnitude meets the grid
  through `rat_h`/`rat_st` as `round_rat` does, and its sign is the exclusive
  or. The value theorem needs that sign to agree with the rational's
  (`quot_signed`, four cases through the `Rat` sign rules).
- Conversion is `round_exact` into the target with the source's sign for
  zero. `convert_exact` says a value the target holds converts to it
  exactly, which covers widening; a theorem that every float of a narrower
  format is a float of a wider one (constructing the target float, with its
  canonical form) is left for the round that needs it.

**Theorems.** Each operation has its value theorem at every mode with no
side condition (`Finite::add_correct`, `sub_correct`, `mul_correct`,
`fma_correct`, `div_correct`, `convert_correct`), its sign theorem
(`add_sign` and `fma_sign` as the exact value's sign or the zero rule;
`mul_sign` and `div_sign` as the exclusive or; `convert_sign`), the exact-zero
results (`add_zero`, `fma_zero`, `sub_self`), and the standard model and
combined error bound for a finite result (`add_model` … `div_model`, through
`Format::model_of` and `bound_of`). Commutativity holds up to value
(`add_comm`, `mul_comm` as `Float::Same`), since the two orders round one
value.

**Special values.** `Float::add`, `sub`, `mul`, `fma`, `div` and `convert`
add IEEE's table on top of the finite operations: NaN propagates, infinities
of one sign add, and `∞ - ∞`, `0 · ∞`, `0 / 0` and `∞ / ∞` are NaN
(`Float::add_inf_opp`, `mul_zero_inf`, `div_zero_zero`, `div_inf_inf`,
`fma_inf_zero` …). A NaN produced from infinities uses the infinity's
evidence (`Specials::nan_of_inf`: a format with infinities has NaN). Division
by zero and conversion may need a NaN the operands do not carry, so they take
the target format's NaN evidence as a parameter that defaults to `trivial`:
it is found at every literal format that has NaN, and refused at the OCP
FP4/FP6 formats, which have neither infinities nor NaN and so have no value
for `0 / 0`; those use the finite operations. A nonzero over zero is the
signed infinity where the format has infinities and NaN otherwise (E4M3). An
infinity converted into a format without infinities is NaN; saturating
conversion (the OCP option) is a policy for `float-bits`.

**API shape.** The finite operations are methods on `Finite` returning a
`Float` (`a.add(b)`, `a.div(b, mode := TowardZero)`), and the special-value
operations methods on `Float`. The mode defaults to `NearestEven`; a default
parameter has no positional slot, so an explicit mode is passed by name.
None of them is a designation of `+` or `*`: the result is a different type
from the operands, and `Float::Same` is not an equivalence on NaN.

**Binary long division.** `round_rat` divided with `Nat::div`, whose state
machine costs the quotient itself under evaluation
([float-round-rat-division-cost](../issues/float-round-rat-division-cost.md)).
`Nat::ldiv` divides `⌊n/2⌋` and doubles, one halving, multiplication,
subtraction and comparison per quotient bit, with `n` itself as fuel and the
recursion stopping at zero; `ldiv_div` and `ldiv_mod` prove it is `div` and
`mod` at a positive divisor, so `round_rat_correct` kept its statement.
`round_rat` and division now evaluate at binary16 (`1/3` computes by `refl`).
The quotient is built as `q * 2`, not `q + q`: a sum of a value with itself
stays a composed run program whose later comparison walks every fragment,
where a multiplication by a literal produces one run.

Observations:

- Binary32 does not evaluate yet, by any route: comparing two numerals past
  about `2^96` built by different routes runs out of fuel in the kernel's
  run cancellation, and an ordinary binary32 value is near `2^150`
  half-units. That is [kernel-wide-run-comparison](../issues/kernel-wide-run-comparison.md);
  the tests evaluate at binary16 and E5M2 and state everything else at an
  open format.
- `nat.hthr` cannot import `omega` or `ring`, so `ldiv`'s proofs are by hand
  over the additive kit; the low bit of the numerator comes from a
  comparison (`Succ(2h) ≤ n`), not a subtraction, which keeps them so.
- A method call on a `match` expression has no carrier
  (`(match c { … }).SignIs(s)` is refused), and an inner `match` in an
  argument needs a motive (`as λ _ => Float(F)`); the module writes
  `Float::SignIs(match … as λ _ => Float(F) { … }, s)`.
- `Fin(b)` in a position with no expected type resolves to another
  constructor named `Fin`; the special-value theorems write `Float::Fin`.


### 14.1 Square root ([float-sqrt](../issues/float-sqrt.md))

Landed 2026-10-31 in the same module, closing `float-arith`. The square root
of a float is irrational in general, so it has no rational exact value to
hand `RoundsTo`, and the issue offered two statements: `RoundsTo` at the
reals (waits on `float-reals`), or a second relation `RoundsToSqrt` with
every clause rewritten (duplicates `RoundsTo` and its laws). Neither was
needed.

**The statement: a cell, not a value.** Every clause of `RoundsTo` compares
the exact value only with half-unit grid points: floats, midpoints of
neighbouring floats (a float is two half-units, so their midpoint is a grid
point), the overflow threshold `F.ovf()` and zero. So a correct rounding of
`√x` is the same thing as a correct rounding of any rational on the same side
of every grid point as `√x`. `Format::SqrtCell(x, y)` says `y` is such a
rational, with each comparison against `√x` read as one against `x` through
`Format::RootLe(m, x)` (`m ≤ 0 ∨ grid(m)² ≤ x`) and `RootLt` (`m < 0 ∨
grid(m)² < x`):

    (m: Int) → (grid(m) ≤ y ↔ RootLe(m, x)) ∧ (grid(m) < y ↔ RootLt(m, x))

The value theorem is `Finite::sqrt_correct(a, mode, nan, nn: 0 ≤ a.val(),
y, cell: F.SqrtCell(a.val(), y)): RoundsTo(F, mode, y, a.sqrt(…))`: one
relation, all of `RoundsTo`'s laws (uniqueness, the error model) apply at any
`y` in the cell. The cell is never empty (`Finite::sqrt_witness_cell`, a
quarter-unit point when the root is inexact) and is exactly what the rounding
reads: given the root's description `SqrtApprox(x, h, st)` (`Approx` with
every bound squared), `SqrtCell(x, y) ↔ Approx(y, h, st)`
(`Format::cell_iff_approx`). When `float-reals` states `RoundsTo` over an
ordered field, the reals' `√x` lies in its own cell and the theorem transfers
by the same argument; until then the cell is the honest form at `Rat`. A test
applies the theorem at a literal: binary16 `√2` rounds `1.414213563`.

**The computation.** `√x` in half-units is the root of `x / 2^(2(qmin-1))
= mag · 2^(bexp + 2 - qmin)`. Writing that as `N / 2^dn` (`sqrt_n`,
`sqrt_dn`; the exponent's positive part scales `N` up), `h =
isqrt(⌊N / 2^dn⌋)` and the root is exact when `h² · 2^dn = N`
(`sqrt_h`, `sqrt_st`, proved as `Finite::sqrt_approx_mag`). Then
`F.round_h(mode, h, st)` rounds it, as every other operation does
(`Finite::sqrt_abs`, the root of the magnitude in every format).
`Nat::isqrt` is in `nat.hthr`: the root `r` of `⌊n/4⌋` first, then `2r`
or `2r + 1` by one comparison of `(2r + 1)²` with `n`, so a root of `b` bits
costs `b` steps; `isqrt_spec` proves `IsRoot`, `r² ≤ n < (r + 1)²`, by hand
like `ldiv`. Binary16 and binary32 roots evaluate by `refl`.

**Signs and specials.** IEEE 754 §9.2 (§6.3 for the zero): `√-0 = -0`
(`sqrt_neg_zero`), a negative nonzero is NaN (`sqrt_neg`), a nonnegative
root carries `+` (`sqrt_sign`), `√+∞ = +∞`, `√-∞` is NaN and NaN propagates
(`Float::sqrt_inf`, `sqrt_neg_inf`, `sqrt_nan`). Like division, `sqrt` takes
the format's NaN evidence (default `trivial`); a format without NaN uses
`sqrt_abs`.

Left for later: the standard model for a root (`|r - √x| ≤ u·√x`) needs
`√x` as a value, so it waits on `float-reals` with the transfer; a cell
member `y` already gets `model_of` at `y`.

## 15. Literals (`float-literal-entry`)

Modules: `lib/std/num/float/window.hthr` (rounding in a window of a format)
and `lib/std/num/float/literal.hthr` (rounding `mant · base^exp`, the
exactness bit, the float instances); the literal types and classes are in
`rat.hthr`. Probes are in `lib/_tests/std/num/float/literal_tests.hthr`;
the inexact warning and the hex refusal are tested in
`crates/elab/tests/lib_std_float.rs`; the lexer's cases are its own unit
tests.

**Surface.** A numeral with a point or an exponent is one token,
`TokKind::Scaled`, holding `mant · base^exp`: `1.5` is `15 · 10^-1`, `1e-3`
is `1 · 10^-3`, `0x1.8p3` is `0x18 · 2^-1`. A decimal point starts a
fraction only with a digit after it, so `1.foo()` and `1..2` keep their
meaning; a hex point only when hex digits and a `p` exponent follow, so
`0xff.f()` stays a method call. A hex float needs its `p` exponent, as in C.
The literal elaborates on the numeral's ladder, like the character and string
literals: at `Decimal` (or `HexFloat`) it is the record of its parts, at any
other carrier it resolves `DecimalLiteral` (`HexLiteral`), and in inference
position it is the `Rat` it denotes. A program writing one imports `rat`.

- `DecimalLiteral<A> { ofDecimal, exact }`. `Rat` holds every decimal
  (`exact` is `True`); `Float(F)` rounds to nearest, ties to even
  (`F.round_decimal(NearestEven, d)`), and its `exact` is `F.decimal_exact(d)`.
  The elaborator asks the kernel's conversion whether the bit is
  `Decimal::inexact()` (`False`), and if so raises the `inexact-literal`
  warning. Overflow to an infinity counts as inexact.
- `HexLiteral<A> { Ok, ofHex: (h) → Ok(h) → A }`. The elaborator passes
  `trivial` as the proof, so a carrier's `Ok` decides acceptance:
  `Float(F)`'s is `F.hex_exact(…).IsTrue()`, and a hex float with a bit past
  the format's precision is refused with a message that says so.

**Why a window.** `round_rat` works in half-units of `2^qmin`, which at
binary64 means a numerator about 1075 bits wide, an exponent search over 2046
binades, and an overflow limit `2^2046`. With the kernel's depth budget at
2048 (PR #187) `pow(2, 1075)` evaluates, but `pow(2, 2046)` and a full-width
`ldiv` (one nested call per numerator bit) still run out, so `round_rat`
does not evaluate at binary64, and it would be slow if it did.
`F.window(j, c)` is `F` cut down to `c + 1` binades from `emin + j`: the
same precision and specials, `emin + j` for `emin`, `c` for `span`. Its
floats are `F`'s floats of those binades with the exponent field lowered by
`j` (`win_up`, `win_down`). `Format::window_rounds` proves that a correct
rounding in the window, read back in `F` (`F.widen`), is a correct rounding
in `F`, at every format and mode, when the value is `InWindow`: nonnegative,
at or above the window's least normal unless `j = 0`, and below its top
binade unless the window reaches `F`'s top. The proof places every float of
`F` (`win_region`): below the window's least normal or from its top binade
on, a float is on the far side of some window float, so it neither rounds
the value nor beats one that does.

**`round_scaled`.** For `x = mant · base^exp`, `win_j` estimates the binary
exponent from the mantissa's width and `⌊exp · log₂ base⌋`, using
`lg ≈ 2^16 · log₂ base` (217706 for ten, exact for two), and starts the
window one binade below it, with `c = min(3, span)`. Then `x / 2^(qmin_W - 1)`
is the fraction `num / den` (`sc_num`, `sc_den`, with powers by squaring),
divided by `ldiv_fuel` with `prec + c + 1` quotient bits. The quotient and
the remainder are the window's half-units and sticky bit (`sc_approx`,
through `approx_div`). Each of the window's conditions is checked, not
assumed:

- the division fits the fuel (`num < den · 2^fuel`);
- the low end: `j = 0` or `top ≤ h`;
- the high end: the window reaches the top, or `h < top · 2^c`.

When the estimate misses, the fallback is `F.round_rat`, which is correct
but does not evaluate at binary64. Past the fuel in the top window the value
is beyond the window's largest float and its overflow threshold, and
`Format::rounds_beyond` says every such value rounds as `2^fuel` half-units
does. So `1e400` is `∞` in constant work. `round_scaled_correct` holds for
every format, mode, base and estimate, and the estimate only decides speed.

**Exactness.** `Float::exact_scaled` compares `±mag · 2^q` and
`mant · base^exp` by their cross-multiplied numerators, with powers by
squaring. `Float::exact_scaled_reflects` proves the bit `Reflects` the value
being exactly the literal (`Float::Denotes`), both ways.
`F.decimal_exact` and `F.hex_exact` are this bit at the nearest-even
rounding.

**Costs.** These are shapes, not timings. A literal of ordinary magnitude
works on numbers of about `prec + c` bits plus the scaling `base^|exp|`.
The scaling dominates at extreme exponents: `1e-300`, the subnormals, and
values near the overflow limit divide numbers of about a thousand bits, and
`ldiv`'s halving of a wide numerator is the cost there.

**What Rust does, and what this is not yet.** Rust's `dec2flt` tries
Clinger's fast path (an exactly representable mantissa and power of ten
in one floating multiplication), then Eisel-Lemire (a 128-bit product
with a table of powers of five, falling back when the product is too close
to a halfway point), then a big-integer slow path. `round_scaled` is the slow
path's arithmetic placed so that every number stays narrow. Eisel-Lemire is
an enclosure test with a fallback, the same shape as the window's checked
conditions, and is the refinement to make once the rounding runs natively.

Observations:

- `Nat::is_zero` is gone (PR #185 stopped the Nat fold probe from
  re-evaluating recursive arms), so the fuelled recursions (`ldiv_fuel`,
  `pow_sq_fuel`, `Nat::width_fuel`) match `n` and name the successor
  `Succ(k)`.
- An inexact literal in a test draws the warning even when the test is
  pinning the rounded value. There is no per-site allow yet.
- The `rat` import is required because the elaborator names `rat::Decimal`;
  a float client that forgets it is told to add it.
- The printer and its round-trip theorem (Lemma 1, nine and seventeen
  digits) are [[float-printer-round-trip]]: the reading half proved here,
  `round_decimal_correct`, is what that theorem reads back through.

## 16. Interval enclosures (`dyadic-interval-enclosures`)

Modules: `lib/std/num/float/interval.hthr` (intervals, their arithmetic, the
checker) and `lib/std/tactic/interval_tactic.hthr` (the tactic), on
directed rounding and reciprocal bounds added to
`lib/std/num/float/dyadic.hthr`; the arithmetic shift `Int::shr` is in
`int.hthr`, `Nat::width` moved to `nat.hthr` from `literal.hthr`, and the
reciprocal-order facts (`le_recip_of_mul_le`, `recip_le_recip`,
`recip_neg`, `mul_le_mono_r_nonpos`) are in `rat.hthr`. Probes are in
`lib/_tests/std/num/float/interval_tests.hthr`. The design follows
CoqInterval's original arithmetic (`docs/coq-hardware-floats-survey.md`
§6.1).

**Rounding at a precision, on `Dyadic` itself.** `d.down(p)` shifts the
mantissa right until `p` bits are left (`Int::shr` floors at either sign)
and adds the shift to the exponent; `d.up(p)` is `-((-d).down(p))`. The
issue sketched `Format::round_dyadic` with a wide format as the precision
knob. That route carries a bounded exponent span and overflow to infinity
or saturation, which an enclosure has no use for, and its proofs are a
rounding relation's; the shift needs one lemma (`Int::shr_mul_le`) and is
sound at every shift amount, so how many bits `Dyadic::cut` drops is a cost
choice with no proof attached. A reciprocal of a positive `m · 2^e` is
`⌊2^K / m⌋ · 2^(-e-K)` below and its successor above, with
`K = p + width(m)`.

**Intervals.** `inductive Interval { Bnd(lo, hi: Dyadic), Whole }`.
`I.Has(x)` reads `lo <= x <= hi` at `Rat`, and `Whole` holds everything.
Every operation is total: a reciprocal of an interval that may hold zero is
`Whole`, and `Whole` absorbs every operation it meets. A pair with crossed
bounds holds nothing, so every containment theorem holds of it vacuously,
which is CoqInterval's reading and needs no well-formedness field. The
operations are `neg` (exact), `add`/`sub` (bounds rounded outward), `mul`
(the four corners' least and greatest, rounded outward; two intervals above
zero skip the search, a sign read off the mantissas), `recip` (positive
intervals reverse the bounds, negative ones are the positive case under
negation), constants (`of_rat`: numerator times the denominator's
reciprocal), and `pow` by squaring. Each has a containment theorem
(`add_has`, `mul_has`, `recip_has`, `pow_has`, …).

**The checker.** `IntervalExpr` names a rational expression (`ILit`,
`IAdd`, `ISub`, `INeg`, `IMul`, `IRecip`, `IPow`). `IntervalExpr::eval`
spells each node as the operation itself, so `a.eval() < b.eval()` converts
to the goal written directly and nothing reduces the exact value.
`lt_search` / `le_search` try a precision and double it on a miss, `tries`
times; the verdict is a `Bool` proved `= True`, the evaluation route the
library uses for closed facts (an `IsTrue` discharged by `trivial` runs out
of the elaborator's fuel on the same goal), and `lt_of_search` /
`le_of_search` turn it into the order.

**The tactic.** Clients write `by intervals()` (or `intervals(p := …, tries
:= …)`; 32 bits and four tries by default), from
`lib/std/tactic/interval_tactic.hthr`. It is a `Tac<Expr>` in Heather: it
views the goal as `Rat::Lt` or `Rat::Le` of two sides, reads each side by
its heads (`Rat::add`, `sub`, `neg`, `mul`, `recip`, `npow`, compared by
global identity) and makes any other subterm a literal, asks the elaborator
whether the verdict is `True`, and returns `lt_of_search(l, r, p, tries,
interval_verdict)`. The reader is untrusted: the proof is checked at the
goal like any term. Asking for the verdict first is what lets a miss fail
with the tactic's own reason ("the enclosures do not separate the two
sides") rather than as a refused proof; a literal that does not compute (a
variable) fails the same way. `Lookup` names functions and types but not
constructors, so the tree is built through wrapper functions
(`interval_lit`, `interval_add`, …) that unfold to the constructors. Probes
are in `lib/_tests/std/tactic/interval_tactic_tests.hthr`, its refusals
included; `(1 + 1/1000)^1000 < 2.719` goes through the tactic as it does by
hand.

**Enclosures of reals** (`interval-creal-enclosures`). Module
`lib/std/num/float/creal_interval.hthr`, with the order facts it needs in
`creal.hthr` (`neg_le`, `mul_le_mono_r_nonpos`, `le_by_sign`, and a real's
distance to its terms, `le_term_add` / `term_sub_le`) and the termwise
rearrangements behind them in `rat.hthr`. `I.HasReal(x)` is `I.Has` read at
`CReal`, `lo <= x <= hi` with the bounds embedded by `CReal::ofRat`. Every
operation keeps it (`add_has_real`, `mul_has_real`, `pow_has_real`, and
`recip_has_real` at an apartness proof, below), by the corner arguments of the rational proofs with
`CReal`'s monotonicity in place of `Rat`'s. The one step that does not carry
over is the case split on the other factor's sign in a product: the
rationals decide it and the reals never do. It is not needed: a `≤` between
reals is a refutation (`¬(y < x)`), and inside one the excluded middle on
`y < 0` is free, which is `CReal::le_by_sign`. A real is enclosed from its
own terms: the n-th is within 1/(n+1) of it, so `x.enclose(n, p)` rounds
`[x_n - 1/(n+1), x_n + 1/(n+1)]` outward (`Interval::span`), and
`CReal::lt_of_enclose` decides `x < y` when two enclosures separate.
`RealExpr` is the checker at `CReal`: `RRat(q)` leaves are enclosed exactly,
as `IntervalExpr`'s are, and `RReal(x)` leaves from their terms at index `n`;
`RealExpr::lt_search` reads twice as far out and one bit finer on a miss.
The tactic reads goals at `CReal::Lt` / `CReal::Le` into it, with
`CReal::ofRat(q)` an exact leaf and any other real a leaf read from its
terms, and takes the starting index as `n := …` (1023 by default). It looks
the `CReal` relations up only when the goal is not at `Rat`, so a client
that never imports `creal` is unaffected. A real leaf costs one term at the
index read; a real whose terms are expensive far out (a series summed to
its index) wants a small starting `n` and more tries. Probes are in
`lib/_tests/std/num/float/creal_interval_tests.hthr` and
`lib/_tests/std/tactic/interval_tactic_real_tests.hthr`.

**Reciprocals of reals** (`interval-creal-reciprocal`). `x.inv(h := h)` takes
a proof that `x` is apart from zero, and a tree cannot carry a proof about
its own value (that would be an inductive-recursive definition). So the
node is `RInv(a, x, h)`: the tree `a` that encloses `x`, the real `x`, and
`h` about `x`. `RealExpr::Wf` asks that each such `a` denote its `x`, and
every theorem about a search takes the two sides' witnesses. A tree the
tactic reads off a goal denotes `x` by conversion, since `eval` spells the
operations, so its witness at an inverse is `CReal::same_refl(x)`; the
tactic builds the witness beside the tree, through wrapper theorems
(`interval_wf_add`, …, `interval_wf_inv`). A tree with no inverse is well
formed by evaluation (`RealExpr::wf_plain`). The enclosure of `RInv(a, …)`
is `a`'s reciprocal, and its containment (`Interval::recip_has_real`) is
the rational proof at `CReal`: inversion reverses `≤` between positives
(`CReal::inv_le_inv`, from `OrderedField::recip_lt_recip`), and a negative
interval is the positive case under `CReal::inv_neg`. The value never reads
the proof's gap, so an inverse whose apartness is a hypothesis is still
enclosed, where a leaf's terms would be stuck. Apartness comes from
enclosures as well: one that excludes zero shows its real apart from zero
(`Interval::apart_of_excludes`), and `RealExpr::apart_of_search` proves
`a.Apart(b)` by separating the two sides either way. The tactic proves
`x.Apart(y)` goals at `CReal` with it, which is how `x.inv(h := by
intervals())` is written.

**Series and elementary functions** (`interval-elementary-functions`).
Module `lib/std/num/float/series.hthr` sums a `Series`, given by its first
term, the ratio of each term to the next, and a `start` past which every
ratio is at most 1/2 in size. Past `start` the tail is dominated by a
geometric one: with `err(N) = 2|t_N|`, the partial sums move by at most
what the error falls by (`Series::tail`), and `j` more steps divide the
error by `2^j` (`Series::decay`, written `1/(ones(j) + 1)` with
`Nat::ones(j) = 2^j - 1`, so the bound needs no subtraction). The limit is
the real whose n-th term is the partial sum `width(scale · (n+1) + n)`
digits past `start` (`Series::index`, with `n <= ones(width n)` from
`nat.hthr`), and it lies within `err(N)` of every partial sum past `start`
(`Series::below`, `Series::above`), which is also how a series that stops
is shown to sum exactly (`Series::same_of_exact`). Its enclosure needs none
of the real's terms: the last term and the partial sum are carried as
intervals by `Interval`'s containment at `Rat` (`Series::box`, each ratio
rounded outward by `of_rat`), the sum is widened by twice the largest
magnitude in the term's interval (`Interval::widen`), and summing stops once
that magnitude is below `2^-p` (`Series::settle`, at most `4p` terms; any
stopping point past `start` encloses the real, so the test is a heuristic
with no proof). `lib/std/num/float/elementary.hthr` instantiates it:
`CReal::exp_rat(a)`, `sin_rat`, `cos_rat` at rational arguments, with the
ratios `a/(k+1)`, `-a²/((2k+2)(2k+3))`, `-a²/((2k+1)(2k+2))` and `start`
from `c = ⌊|a|⌋ + 1` (`Rat::abs_ceil`; twice it for exp, once for sin and
cos, where each step is two degrees). Containment is stated against these
reals, which are the functions' definitions at rationals until
`real-functions-and-derivatives` gives them at `CReal`; the three are exact
at zero (`CReal::exp_rat_zero`, …). The checker reads such reals through a
leaf of their own: `Enclosed` packs a real with enclosures at every index
and precision and the proof that they contain it, and `RBox(b)` is that
leaf, so `creal_interval` knows nothing of series. The tactic reads the
heads `CReal::exp_rat`, `sin_rat`, `cos_rat` as `RBox(CReal::exp_box(q))`
and so on when they resolve where it runs; `2 < exp(1) < 3`,
`0.84 < sin(1)`, `23 < exp(355/113)` and `sin(1)² + cos(1)² < 1.001` go
through `by intervals()` (`lib/_tests/std/num/float/elementary_tests.hthr`).
A step costs the outward rounding of its ratio, a reciprocal at `p` bits,
which dominates the product and the sum beside it; a series needs about
`p` plus the size of its term at `start` in bits of steps.

**Costs.** These are shapes. An operation at `p` bits costs its roundings,
each about `p` halvings for the width and `p` for the shift, plus the
exponent alignment of its comparisons. `Dyadic::le_dec` now compares
mantissas aligned to the smaller exponent (`Dyadic::aligned`), so it
computes one power of two, of the exponents' gap, where the rationals'
cross products computed four, of the exponents themselves, and
`Finite::le_dec` inherits it. With the direct product above zero, that cut
an interval product by about an order of magnitude. A power costs
`O(log n)` products.

**What the checker does not do.** An equality is never decided (a third is
never exact, so `3 · (1/3) <= 1` is refused at every precision; the probes
pin the refusal). Products of an interval with itself are bounded as if
independent, so a goal that needs the dependency (`x - x`) widens. Left:

- `log`, by the atanh series after reducing the argument, and argument
  reduction for `exp`, `sin` and `cos`, whose cost is otherwise linear in
  the argument ([[interval-log-and-reduction]]);
- the functions at real arguments, and their laws (`exp(a + b) ≈ exp(a) ·
  exp(b)`, `sin² + cos² ≈ 1`), which want continuity and `CReal` series
  ([[elementary-functions-at-reals]]).
