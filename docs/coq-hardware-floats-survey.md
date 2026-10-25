# Hardware floats in Coq: what the paper means for Heather

Status: **survey**, 2026-10-25. Source: Érik Martin-Dorel, Guillaume
Melquiond, Pierre Roux, *Enabling Floating-Point Arithmetic in the Coq Proof
Assistant*, Journal of Automated Reasoning 67(33), 2023
(<https://inria.hal.science/hal-04114233>, CC BY 4.0), committed beside this
note as `docs/hal-04114233.pdf`. Section numbers below are the paper's.
Follow-up is in §8. Read against master at `9470549`.

The paper reports on Coq's *primitive floats*: an abstract kernel type
`float` whose operations reduce by calling the processor's binary64 unit,
tied to the logic by axioms against a naive executable specification
(`spec_float`), which Flocq then proves equivalent to "round the real
result". It then ports two libraries that prove theorems about reals by
computing with floats, ValidSDP (polynomial positivity by a floating-point
Cholesky check) and CoqInterval (interval arithmetic), and measures them.

Minus does not plan floats the way the paper does, and the paper is mostly
about one mechanism Heather's kernel policy already rules out (§2). Its
value for Heather is elsewhere: in what its soundness bugs say about any
fast path, in the shape of its specifications, and in four library ideas
that `lib/std/num/float/` can take directly.

---

## 0. The answer in brief

1. **Heather should not add primitive floats to its kernel, and the paper
   shows what it would cost.** Coq's mechanism is axiomatic symbols plus
   hard-coded reduction rules plus about a dozen specification axioms. That
   is a kernel case for a definition, which Heather's acceleration policy
   (`crates/kernel/DESIGN.md`, `issues/kernel-acceleration-policy.md`)
   retired. The paper's own bug list (§3.4) is a catalogue of how such a
   fast path goes wrong. §2 says what the only policy-compatible version
   would look like, and why there is no customer for it.
2. **Heather's float design is already the paper's two-layer specification,
   with no axioms between the layers.** Coq has three layers: the primitive,
   the operational `spec_float` reference, and Flocq's "result = round(exact)"
   theorems. It glues the first two with axioms. Heather has only the bottom
   two: the executable rounding *is* the definition, and `RoundsTo` is the
   relation it is proved to satisfy. The paper's remark that the operational
   layer is "complete but useless in isolation" (§2) is the argument for
   `RoundsTo` (§3).
3. **Collapsing NaN payloads in the logic, and the paper's equality bugs,
   support decisions Heather already made.** These are design 7.2's payloads
   at the bits layer and §4.1's structural `=`. The paper adds one thing
   Heather has not written down: what the native lane must assume about the
   machine (MXCSR, no x87, a NaN policy). §4 lists those assumptions.
4. **Four library ideas port directly.** (a) A sharper standard model: the
   relative bound `u/(1+u)`, relative and absolute error never both nonzero,
   and exact subnormal sums. (b) Outward rounding by "nearest, then step
   outward". (c) Literal entry and printing, with a round-trip theorem that
   Heather can prove about its own in-language printer. (d) Conformance
   vectors for binary32 taken from the host's IEEE unit. See §5.
5. **Two ideas reach beyond floats.** Interval enclosures over `Dyadic` at a
   chosen precision would let Heather prove inequalities about real
   expressions by evaluation. Making an interpretation total (an ill-formed
   input denotes the empty set) is an alternative to carrying evidence. See
   §6.
6. **The benchmarks say back what Heather's perf diary already says.** Once
   the arithmetic got fast, list traversal dominated the proofs (§5).
   Compiling proofs to native code paid off only for long runs. See §7.

## 1. What the paper contributes

- **§2.1, the specification on Coq's side.** `Primitive float :=
  #float64_type` and one `Primitive` per operation (`add`, `sub`, `mul`,
  `div`, `sqrt`, `abs`, `opp`, three Boolean comparisons, a four-valued
  `compare`, `classify`, `of_int63`, `normfr_mantissa`, `frshiftexp`,
  `ldshiftexp`, `next_up`, `next_down`). All are round-to-nearest-even only.
  There is a concrete `spec_float` (signed zero, signed infinity, one
  payload-free NaN, and unnormalised finite `s m e`), the conversions
  `Prim2SF` and `SF2Prim` (whose round-trip and validity facts are axioms),
  and one axiom per operation, such as `Prim2SF (add x y) = SFadd 53 1024
  (Prim2SF x) (Prim2SF y)`. `SFadd` is deliberately naive: it aligns by
  shifting left to the smaller exponent. About 500 lines in all.
- **§2.2, Flocq's side.** `binary_float` is `spec_float` with a validity
  proof on the finite case. `Prim2B`/`B2Prim` are morphisms
  (`add_equiv: Prim2B (x + y) = Bplus mode_NE …`), which gives access to
  `Bplus_correct`: the real value is the rounding of the real sum, unless it
  overflows. Added for the purpose: Boolean comparisons, `Bldexp`,
  `Bfrexp`, `Bsucc`, `Bpred`, `Bulp`.
- **§3.1, the reduction engines.** There are three: conversion, `vm_compute`
  (bytecode) and `native_compute` (OCaml compiled). Each needs the rule
  "fully applied to literals: call the FPU, otherwise build a stuck term".
  Floats are boxed, which collides with OCaml's unboxed float arrays.
- **§3.2, rounding directions.** Only nearest is supported, because neither
  C nor OCaml can change the rounding mode safely (GCC bug 34678). Interval
  arithmetic instead rounds to nearest and then takes `next_down`/`next_up`.
  That is sound but not tight. The cost of the second allocation is removed
  by a peephole rule that reuses the first box.
- **§3.3, parsing and printing.** Raw terms print as exact hexadecimal
  (`0x1p+0`). Notations print as 17 significant digits, justified by a Coq
  proof (`Print17`) of the general Lemma 1: if `β^p < β'^(p'-1)`, then any
  `x'` within half a unit of the `p'`-th radix-`β'` digit of a float `x`
  rounds back to `x`. A decimal that is not a binary64 value draws a
  warning.
- **§3.4, soundness.** Four kinds of threat, each with real bugs that were
  fixed. *Specification typos*: `leb` was wrong, and zeros were classified
  inconsistently; an unused-pattern-variable warning would now catch the
  first. *Engine or hardware disagreement*: x87 double rounding forced a C
  implementation on 32-bit platforms, plus a start-up test. *Convertibility
  versus IEEE equality*: `-0 = +0` and `NaN ≠ NaN` under IEEE, and the
  kernel needs the opposite on both. *Interaction with other primitive
  types*: unboxed float arrays broke persistent arrays and
  `native_compute`, and one of those breaks proved `False`.
- **§4, applications.** ValidSDP's specification is a tower of records:
  `Float_spec` (a rounding operator, `ε`, `η`, and the model `◦(xy) =
  (1+d)xy + e` with `|d| ≤ ε/(1+ε)`, `|e| ≤ η`, `de = 0`), then
  `Float_infnan_spec` (a concrete type with NaN and infinities, and a
  finiteness predicate), then `Float_round_up_infnan_spec`. Several
  instances fill it: unbounded-exponent `flx64`, binary64, CoqInterval's
  emulated numbers, and the primitives. The port only added instances.
  CoqInterval's port was intrusive. Its specification claimed exact directed
  rounding, so `add` became `add_UP`/`add_DN` with an enclosure-only
  specification. Its `-∞`/`+∞` edge cases were handled by giving every
  ill-formed interval the meaning "empty". `fromZ` is specified only on
  `[-256, 256]`, `midpoint` is unspecified, and exact operations became
  tight intervals.
- **§5, benchmarks.** Individual operations ran 57–243× faster. Whole proofs
  ran 10–20× faster: at most 22× for Cholesky, and 10–20× for most of the
  101 CoqInterval goals. In the hardware runs, list manipulation dominated.
  Four goals failed because outward rounding is not exact (`1 + 1 ≤ 2` at
  one bit). Compiling proofs to native code paid off only for long runs,
  because compiler latency dominates short ones.

## 2. The kernel: why not, and the only version that could fit

Coq's mechanism has two parts. Axiomatic symbols get reduction rules, and
the rules are justified by axioms against a reference implementation. In
Heather's acceleration policy, the first part is the retired third kind,
"pattern-matching on a definition's spelling". The paper even contrasts
`Primitive` with the earlier *retroknowledge* mechanism (§2.1), which
"hardcoded some reduction rules for these operations (thus sidestepping
their original definitions)". That is the shape Heather retired. The second
part could be written as Heather `axiom`s (`docs/axiom-provenance-design.md`),
but an axiom is an opaque global: it can state `add_spec`, and it cannot make
`add` reduce. So the rules would still be kernel cases, and every theorem
proved by evaluation would sit on axioms its statement does not show.

What the policy does allow is a **representation change with an adequacy
argument, generic over the type**: `Val::NatRun` and `Val::BitRun`. A
float representation does not fit that mould, for three reasons.

- A `Finite(F)` value is already three fields, and its `Nat` fields already
  ride on runs. Representation was never the cost. The operations are: each
  one is a `round_h` over shifts, comparisons and a division. A faster value
  representation does not make `Format::round_h` faster unless the evaluator
  recognises `round_h`, and recognising a definition is the retired kind.
- The run accelerations classify a fold's step *by evaluating it on fresh
  neutrals* (`eval/probe.rs`). A rounding is not a fold, so there is nothing
  to classify.
- What the kernel trusts from its numeral crate today is small: `is_zero`,
  `pred`, the order, and limb arithmetic. All of it is integer arithmetic on
  `u64`. A float unit would add the trust the paper spent §3.4 on. That
  covers double rounding, the rounding mode, NaN payloads (Rust's own float
  semantics leave NaN bit patterns nondeterministic, the same choice the
  paper makes in the logic), and every interaction with the existing
  representations.

The one shape that could someday fit is the "verified fancy kernel" note in
the acceleration policy. The kernel would gain a fast path whose rule is
*proved* in Heather-in-Heather to agree with the library definition
(`Finite::add` and so on), leaving only "the FPU computes IEEE binary64
round-to-nearest" as trusted. That is the paper's `add_spec` turned from an
axiom into a theorem about everything except the silicon. There is no
customer for it. Nothing in Heather proves real-number facts by heavy float
computation, and the native lane needs float *semantics* to compile against
(§4), not fast in-kernel floats. If a customer appears (an interval tactic,
§6.1, whose goals run too long), the first answer under the policy is still
the library one: run fewer bits (CoqInterval's 30-bit default was enough for
87 of its 101 goals, Fig. 2) and keep the operations' cost proportional to
their bits.

## 3. What Heather's float design already does the same way, minus the axioms

| the paper | Heather (`lib/std/num/float/`, `docs/floating-point-design.md`) |
|---|---|
| `spec_float`: unnormalised `s m e`, payload-free NaN | `Float(F)` with canonical `Finite(F)` (`IsTrue` validity), payload-free `NaN(has)`; payloads deferred to `float-bits` (§7.2) |
| `binary_float` = `spec_float` + validity proof | `Finite(F)` carries `ok: F.canonical(mag, bexp).IsTrue()` from the start |
| `SFadd`: naive left-shift alignment | `Format::round_h` over half-units: the simple routine, proved, not the fast one |
| axiom `Prim2SF (add x y) = SFadd …` | none needed: the executable is the definition |
| Flocq `Bplus_correct` (value is the rounding of the real sum) | `Finite::add_correct`: `RoundsTo(F, mode, exact, result)` at every mode |
| side condition "no overflow", sign "omitted for conciseness" | value theorem with no side condition plus a separate sign theorem (design P9, `round_signed_sign`) |
| only round-to-nearest-even | all five modes, exactly, because nothing is delegated |
| `Bsucc`/`Bpred`/`Bulp` added for intervals | `Finite::next_up`/`next_down` with spacing, `Format::ulp_at` |

Two points are worth stating outright. First, the paper's motivating
complaint, that the operational layer "explains how the numbers are computed
but not what their properties are", is the reason design P6 made the
specification a relation. Heather got there from flean's side, and the paper
gets there from Coq's. Second, the paper's trust argument for its
operational layer is that Flocq proves it equivalent to rounding (§2.2: this
"brings confidence in the correctness of the non trivial bit-level
specification"). In Heather the executable needs no such argument. It is
proved against `RoundsTo`, so a typo in `round_h` cannot survive. But
`RoundsTo` itself is guarded only by its own probes and by the laws proved
about it (uniqueness, monotonicity, bracketing). A wrong clause that still
satisfies those laws, such as a wrong tie rule or a wrong overflow
threshold, would pass. The paper's two specification bugs are exactly this
kind of slip. §5.4 gives Heather the same external check the paper gets from
the hardware.

## 4. The native lane: assumptions to write down before float codegen

FunctionIR already treats floats as semantic types whose register class is
lowering's business (`docs/function-ir-design.md` §2.2), and the x86 model
has no SSE yet. The paper's §3.2 and §3.4 name what the lane will have to
assume about the machine. Each item below is a premise of the program logic,
not a library theorem.

- **The rounding mode is ambient machine state.** A compiled SSE `addsd`
  means "round to nearest even" only under `MXCSR.RC = 00`, and it means
  "IEEE" only with flush-to-zero and denormals-are-zero clear. A Linux
  process starts with `MXCSR = 0x1F80` (all exceptions masked, nearest, FTZ
  and DAZ off). The Linux spec (`lib/std/os/linux/`) should say so, and every
  float instruction's step form should take the MXCSR fields as inputs
  rather than assume them. A `Mode` argument then has an honest lowering:
  either a constant mode with an MXCSR write proved around the region, or
  the paper's trick below.
- **Directed rounding without touching MXCSR is "nearest, then step
  outward".** It is sound for enclosures and off by at most one ulp
  (§3.2). An interval kernel compiled this way would keep MXCSR constant. The
  library side is a theorem (§5.2).
- **Never x87.** Double rounding through the 80-bit stack is the paper's one
  hardware-level bug class. The lane should select SSE2 scalar instructions
  only and state that as a selection rule, not a convention.
- **NaN bits are a platform policy.** x86 SSE produces the default NaN
  (`0xFFF8…` for binary64) from invalid operations and propagates the first
  NaN operand, quietened. Design §7.2 already plans this as a record. The
  paper adds that the *logic* must not depend on it, which `Float(F)`'s
  single `NaN` guarantees.
- **Compiler identities live at `Float(F)`, not at IEEE equality.**
  `x + 0.0 → x` is wrong at `-0`, and `x == x → true` is wrong at NaN. These
  are the paper's convertibility bugs seen from the compiler's side. A
  verified selection rule is proved against `Float(F)`'s structural `=`,
  where `Finite::sub_self` and the sign theorems already say what is true.

None of this is work yet. It belongs in the design note of whichever round
first lowers a float operation, and §8 logs it there.

## 5. Library ideas for `lib/std/num/float/`

### 5.1 A sharper standard model

ValidSDP's `Float_spec` states `◦(x ∘ y) = (1 + d)(x ∘ y) + e` with three
refinements over Heather's `Format::error_bound` (`|r - x| ≤ u·|x| + η`):

- `|d| ≤ u/(1 + u)` rather than `u`. This is the optimal relative bound for
  the nearest modes (Jeannerod–Rump, the paper's ref. 18). It is free once
  the cell picture of design §13 is in place: the worst case is the midpoint
  just above a power of two.
- `d·e = 0`: the error is relative *or* absolute, never both. The normal and
  subnormal cases already split this way in `relative_error` and
  `subnormal_error`. The combined statement keeps the split instead of
  adding the two bounds.
- For **addition and subtraction, `e = 0`**: a sum whose rounding lands in
  the subnormal range is exact, since both operands are multiples of `2^qmin`.
  Error analyses of sums (Kahan summation in `float-eft`, the dot products
  of `ml-scalar-refinement`) then never pay `η`.

Design §13 already left the bound relative to the *result*,
`|r - x| ≤ u·|r|`, for later. It belongs in the same round. Filed as
`issues/float-error-sharper-model.md`.

### 5.2 Outward rounding

The paper's interval libraries rely on one unstated fact: `next_down` of the
nearest rounding is at most the rounding toward `-∞`, and dually for `+∞`.
Heather has both sides (`next_up_spec`, `rounds_ge_down`, `rounds_le_up`),
so this is a short theorem. It is what a compiled interval kernel (§4)
would cite. It goes in the same issue.

### 5.3 Literal entry and printing

Heather has no float or decimal-fraction literals. Numerals are the only
`Rat` and `CReal` constants (PR #78), and `radix-numerals-design` covers only
integers. When float literals come, the paper's design carries over, and
Heather can do the part Coq could not:

- An **exact hexadecimal spelling** (`0x1.8p3`) for every finite float,
  extending the radix-numeral grammar. It is the raw printing form, which
  never loses information.
- A **decimal spelling that rounds** by `Format::round_rat` at the expected
  format (the format is carrier-directed, like numerals), with a warning when
  it is inexact. That warning is Coq's, and `round_rat_exact` decides it.
- A **printer whose round trip is a theorem.** Coq prints through `printf
  "%.17g"` and calls in-language printing (Number Notation) a possible
  future with a speed cost (§3.3). Heather's printers are in-language
  already (`docs/parser-canonical-printers-design.md`), so Lemma 1 (`β^p <
  β'^(p'-1)` gives a lossless round trip at `p'` digits) can be proved for
  every `Format`. Seventeen digits for binary64 and nine for binary32 are
  then corollaries.

Filed as `issues/float-literal-entry.md` (language, with `math-float` as
customer).

### 5.4 Conformance vectors from the host

The paper checks its specification against the hardware by running both
(§3.4). Heather can do this the other way round, with no change to the
kernel. A small generator uses the host's IEEE binary32 unit (Rust `f32`,
round-to-nearest-even) to write a `lib/_tests` probe file of `refl`
theorems: `Finite::add(a, b) = expected` for chosen operands, at the edges
the specification is most likely to get wrong. Those edges are ties to
even, overflow thresholds, the subnormal boundary, `x - x`, and signed zeros
through `fma` and `div`. Binary32 evaluates by `refl` since the kernel's
wide-run comparison fixes. The probes check the *specification* (`RoundsTo`
plus the special-value table) against an independent implementation, which
the internal proofs cannot do (§3). The same vectors later serve the native
lane's SSE step forms. Filed as `issues/float-conformance-vectors.md`.

### 5.5 Specify by what proofs use

CoqInterval's port is a lesson in specification width. The interface that
claimed exact directed rounding could not take the cheaper implementation.
The interface that claims only enclosure could. `fromZ` correct on
`[-256, 256]`, `midpoint` unspecified, and heuristics with no theorem at all
are the same choice: a function that only steers a search needs no
correctness statement, because the certificate is checked anyway. Heather's
`Rounding(F)` record (design §5.4, faithful plus monotone) is the right
width for algorithms that tolerate any faithful rounding. The ML refinement
(`issues/ml-scalar-refinement.md`) should be written against such an
interface, like ValidSDP's `Float_spec` tower, so that `Float(F)` and an
unbounded-exponent model are both instances. Logged there.

## 6. Ideas beyond floats

### 6.1 Interval enclosures over `Dyadic`

CoqInterval proves goals like `|∫₀⁸ sin(t + eˣᵖᵗ) dt - 0.3474| ≤ 0.1` by
computing enclosures. Its original, emulated arithmetic was exactly the shape
of Heather's `Dyadic`: an integer mantissa, an integer exponent, an
unbounded exponent, no infinities, and every operation at a requested
precision with an exact directed rounding. Heather has all of that already:
`Dyadic`, and `Format::round_dyadic` at `TowardNeg`/`TowardPos` for any
`Format`. So an enclosure library needs no floats at all. It needs a
`Format` with a wide exponent span, intervals of dyadics, the arithmetic
and elementary-function enclosures with their containment theorems, and a
reflective tactic that evaluates them. Two findings from the paper shape it:

- **Precision is a knob.** In Heather, unlike on a fixed FPU, evaluation cost
  scales with the bits carried, so a tactic should start low and refine. The
  paper's 30-bit default sufficed for most goals (Fig. 2).
- **Make the interpretation total.** CoqInterval gives every ill-formed
  interval (`[+∞; x]`, `[x; -∞]`) the meaning "empty", so every containment
  theorem holds vacuously on junk, with no runtime check and no
  well-formedness proof field. Heather's habit is to carry the evidence. For
  a reflective checker the paper's choice is cheaper, because the checker's
  verdict is the only thing proved.

The customers are `float-transcendental` (a Ziv loop *is* refining an
enclosure until it misses every breakpoint, design §6), deciding `CReal`
comparisons at concrete arguments, and the ML bounds. The roadmap ranks
decidability and tactics where "tactics pay most". Filed as
`issues/dyadic-interval-enclosures.md` (mathematics, no milestone).

### 6.2 Certificates checked with approximate arithmetic

ValidSDP splits the work the way Heather's certifying arithmetic does
(`docs/certifying-arithmetic-substrate-design.md`): untrusted search, checked
result. Here an external SDP solver returns a witness and an in-logic
computation accepts it. The check runs
in *rounded* arithmetic, and its soundness is an a-priori error-bound
theorem: Rump's corollary turns "float Cholesky of `A - c·I` succeeds" into
"`A` is positive definite". This is a second way, beside exact rationals, to
keep a certificate check cheap. It is the natural showcase for `float-error`
and `float-eft` once a customer needs positivity certificates. It is
recorded here only.

## 7. What Heather's experience says back

- **After the arithmetic, the data structure.** With hardware floats, list
  manipulation dominated the Cholesky proofs (§5.1). Heather's perf diary
  makes the same point repeatedly: the cost moves to whatever is next, and a
  round should attack what `scripts/perf report` says dominates.
- **Compiling the evaluator is a latency trade.** `native_compute` won only
  on long goals, and with hardware floats it was "often detrimental"
  (Fig. 4). Its authors note that fast primitives make it "largely moot",
  shrinking the trusted base. Heather's choice of one environment machine,
  with representation changes and strategies instead of a second compiled
  engine, is the same trade made earlier.
- **Measuring one operation needs a guard against dead-code elimination.**
  The paper duplicates an operation through `select m1 m2 := m1`, because
  both of Coq's compilers drop an unused `let`. Heather's elaborator does the
  same since PR #147 (unspliced `let` values are discarded), so a
  hand-written cost probe must make its duplicate reach the result.
- **Each fast path is tested against the others.** The paper's worst bugs
  came from two primitive types meeting (§3.4). Heather's equivalent is
  `NatRun` and `BitRun` meeting, and every future representation change.
  The differential oracle covers conversion. A new representation should
  also be fuzzed *in combination* with the existing ones, not alone.

## 8. Follow-up

- **Filed** `issues/float-error-sharper-model.md` (mathematics,
  `math-float`): `u/(1+u)`, the exclusive `d·e = 0` model, exact subnormal
  sums, the result-relative bound, and outward rounding (§5.1–§5.2).
- **Filed** `issues/float-conformance-vectors.md` (mathematics,
  `math-float`): host-generated binary32 probes checking `RoundsTo` and the
  special-value tables (§5.4).
- **Filed** `issues/float-literal-entry.md` (language, `math-float` as
  customer): hexadecimal and decimal float literals, the inexact warning,
  and a printer with a proved round trip (§5.3).
- **Filed** `issues/dyadic-interval-enclosures.md` (mathematics, no
  milestone): enclosures over `Dyadic` at a chosen precision, and a
  reflective tactic (§6.1).
- **Logged** on `issues/ml-scalar-refinement.md`: write the scalar interface
  at ValidSDP's width, so that unbounded-exponent and bounded formats are
  both instances (§5.5).
- **Logged** on `issues/floating-point-formalization.md`: this survey, the
  no-primitive-floats conclusion (§2), and the native-lane machine
  assumptions (§4) for the round that first lowers a float operation.
- No kernel follow-up.
