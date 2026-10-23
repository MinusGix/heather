# Arend survey: what Heather should take from the Arend paper

Status: **survey**, 2026-10-23. Source: Part, Isaev and Sinchuk, *Theorem
prover Arend*, arXiv:2610.27264v2 (21 Oct 2026), committed beside this note as
`docs/2610.27264v2.pdf`. Page numbers below are the paper's. Follow-up issues
are listed in §8.

Arend is JetBrains Research's prover for univalent and constructive
mathematics: a variant of HoTT with an interval type (HoTT-I, Isaev 2014), an
IntelliJ plugin, a CLI meant for coding agents, and `arend-lib` (constructive
algebra, locales, analysis, and the HoTT book's synthetic homotopy theory).
This note reads the paper against Heather's design as it stands on master at
`82f4a2d`: the DeLaM kernel with its extensions (`crates/kernel/DESIGN.md`),
the no-UIP groupoid-model argument (`docs/no-uip-model.md`), strict
propositions without `transp` (`docs/sprop-design.md`, 2026-09-30 revision),
the class system (`docs/traits-design.md`), the export lens
(`docs/export-fragment-design.md`) and the areas in `docs/roadmap.md`. As with
the Wick survey, the goal is to learn from Arend, not to port it.

---

## 0. The answer in brief

1. **Arend's headline features are mostly the opposite bet from Heather's.**
   Impredicative `\Prop`, universes indexed by homotopy level, univalence as a
   computing axiom, and interval-based paths all trade canonicity and
   decidable, exportable conversion for extensionality. Heather chose
   predicativity (2026-07-23), irrelevance as a property of fixed formers, and
   evaluation as proof. None of the univalent machinery should be adopted.
2. **The interval is the one kernel idea worth recording properly.** It makes
   function extensionality a definition that computes, and it is compatible
   with Heather's no-UIP groupoid model. But the paper itself admits that
   Arend loses canonicity (closed `Int` terms stuck on a residual `coe`,
   p. 19), the regularity rule is a free-variable side condition that
   conversion must decide, the code recursors grow, and every definitional
   path equation is one Lean cannot replay. Filed as a research issue that
   waits for a puller, not as work.
3. **The adoptable ideas are in the elaborator, the tooling and the library.**
   - Partial implementations: a child class implements inherited fields
     (Arend's `PseudoRing` derives `0 * x = 0` from the additive group).
     Heather's four `CommRing` instances (`Int`, `Rat`, `CReal`, `Dyadic`)
     each hand-supply `zero_mul`/`mul_zero` today. Filed, under
     `math-classes`.
   - The agent-facing CLI: symbol search, proof search by statement pattern
     (`"_ + _ = _ + _"`), find usages, class hierarchy with instance sites,
     scope listing, `--json`, and a daemon that keeps the checked library in
     memory. Heather already owns this as `lemma-selection-and-search`, which
     says it "wants a bigger library to be worth it". At about 2,500
     declarations, Arend's experience says it is worth it now. Logged there.
   - A skills pack for agents (formalize, prove, quirks, error diagnosis),
     which is Arend's answer to "the prover is in no training data". Heather
     is developed almost entirely by agents and has no skills. Filed.
   - Locales built from sites and presentations, and Isaev's cover spaces, as
     direct input to `frame-and-locale-foundations` and `math-reals`. Logged.
4. **Some things Heather already does as well or better.** Arend's `Array`
   (definitional componentwise equality of fixed-length arrays, nested
   recursion with an ih over `Fin`) is Heather's `Vec`/`DVec`/`Wf`, where the
   componentwise comparison falls out of Σ-η and unit-η instead of a special
   rule. Arend's dynamic class blocks with an implicit `\this` are Heather's
   receiver methods and function-owned members.

---

## 1. What Arend's core theory is (pp. 3–10)

- **HoTT-I.** A primitive type `I` with constructors `left`, `right` and one
  eliminator, `coe(λx.A, a, i) : A[i]`, with `coe(…, left) ≡ a` and
  **regularity**: `coe(λx.A, a, i) ≡ a` when `x ∉ FV(A)`. Paths are maps out
  of `I` with fixed endpoints, `Path(λx.A, a, a')`, with `path`/`@`, β, η and
  definitional endpoint laws. `J` is derived (p. 18, via a `squeeze`
  connection built from `coe`), and its β rule holds by regularity.
- **Univalence** as a primitive `iso(A, B, f, g, p, q, i)` with endpoint
  rules and one transport rule along the canonical `iso` line.
- **Inductive types with conditions.** A constructor may compute to another
  term at some arguments (`pos 0 ⇒ neg 0`, or `con= left ⇒ con1`), and
  functions out of the type must respect the conditions. With an `I`
  argument this gives HITs and quotients with computational behaviour
  (Zhang and Isaev, arXiv:2405.12994).
- **Impredicative `\Prop`**, a predicative hierarchy of `\Set n`, and
  universes `Type(n, k)` indexed by homotopy level `k` (a constant, never
  polymorphic). A type proved to be an h-prop or h-set can be *placed* in
  `\Prop`/`\Set` (`\use \level`), and a `\truncated` inductive in a universe
  of level `k` eliminates only into types proved to be `k`-types. This
  **h-prop elimination** gives the principle of unique choice computationally.
- **Subsumptive subtyping** in the core: cumulativity, and record extension
  with **manifest fields** (`x ⇒ a`), multiple inheritance, field type
  overriding, and **property** fields that are ignored when records are
  compared.
- **`Array`**, a built-in record `{len, at : Fin len → A}` with the rule that
  functions on `Fin (n+2)` agreeing pointwise (recursively) are equal.

What Arend does **not** have, by the paper's own account: canonicity
(p. 3: "the MLTT property that every closed term of type Nat evaluates to a
canonical number does not hold in Arend"), a computation rule for `coe` in a
family of path types (p. 21), and structural computation for `iso` and
universe fillers, which §2.5 states as an open problem.

## 2. The interval and paths, read against Heather's kernel

### 2.1 What it would buy

- **Function extensionality as a definition**: `FunExt(f, g, λx.p) :≡
  path(λi. λx. p x @ i)`, with a computing inverse (p. 11). Heather does not
  assume funext (`lib/std/itree/itree.hthr:23`), and that absence is felt in three
  places: tier-2 tree laws hold only up to `ITree::Same` or depth-indexed
  equivalence, `Acc` is not provably a proposition
  (`issues/kernel-v1-extensions.md`, log 2026-07-26), and the setoid
  machinery (`issues/setoid-roadmap-and-resumption.md`) carries what a
  quotient would.
- **J with definitional β, derived rather than primitive.** Heather's `Id`
  and `J` are an extension with four code-recursor branches; under HoTT-I
  they would be definitions over `Path`.
- **No-UIP survives.** Heather's model argument interprets contexts as
  groupoids (`docs/no-uip-model.md` §2). The groupoid `0 ≅ 1` is a
  contractible interval whose endpoint inclusion is a cofibration, which is
  what Isaev's models need (arXiv:2004.14195). `Path` over it is the hom-set,
  that is `Id`; regularity holds strictly because a constant family acts by
  identities; funext holds because `I → Π x. B` and `Π x. I → B` are
  isomorphic groupoids. The strict propositions' construction (§3 there)
  only needs `Γ_{a~b}` closed under isomorphism, which is unaffected. So the
  interval is one of the few extensionality routes that the no-UIP decision
  keeps open. Observational type theory, the other usual route to funext and
  quotients, has UIP built in, which is why `transp` was removed.

### 2.2 What it would cost

1. **Canonicity, and with it evaluation as proof.** Heather leans on closed
   terms evaluating: closed facts are proved by evaluation (`= True` by
   `refl`), and the effectful compiler runs by kernel evaluation first
   (roadmap, `hih-pl-source`). The paper's table on p. 19 shows Arend leaving
   `winding(ℓ · ℓ)`, a closed `Int`, as a residual `coe`. That failure comes
   from `iso`, which Heather would not add, but `coe` in a family of path
   types is stuck too (p. 21), and so is `coe` through any family whose head
   is not regular, unless the kernel gets Isaev's structural rules (p. 25:
   pairs componentwise, functions by transporting the argument backwards,
   paths by adding a coordinate, `Nat` by constructors). Those rules exist
   only as schemata, and their canonicity and normalization are an open
   problem in the paper. For Heather they would also have to cover `W`,
   `Wf`, `IWf`, `Vec`, `DVec`, `M`, sums and the codes.
2. **Regularity is a free-variable test inside conversion.** `x ∉ FV(A)` is
   not stable under reduction unless it is asked of a normal form (a family
   can mention `x` only inside a redex that erases it). Heather's conversion
   is untyped weak-head reduction plus type-directed comparison, transcribed
   from DeLaM ch. 06, with the logical-relation argument of ch. 07–08 behind
   it. The rule needs its own completeness argument there and in heather-coq.
3. **The code recursors grow.** `I`, `left`, `right`, `coe`, `Path`, `path`
   and `@` are about seven new codes and branches on top of today's 65
   (`crates/kernel/DESIGN.md`, the `IWf` paragraph), each with its quoting,
   generator and `count_branches` transcription.
4. **Export loses fidelity.** The exporter already realises conversion that
   exceeds a target's, one former at a time: `Wf` natively in Lean,
   irrelevance by eta-long terms (`docs/export-fragment-design.md` §3, §5).
   Path endpoints, regularity and `path`-η have no such realisation. Lean
   has no type whose functions have definitional endpoints, and `Eq.rec`
   with a constant motive does not reduce on an arbitrary proof. Every proof
   that relied on them would need the exporter to turn conversions into
   explicit rewrites, which is the "exported ⇒ checks" story's hardest case.
5. **The code layer stays safe.** Minus's position that propositionally equal
   functions may differ as code (`issues/kernel-v1-extensions.md`, the funext
   earmark) holds unchanged: `Path` is propositional and `□` conversion stays
   syntactic, as long as no rule derives `□`-level equality from a path.

**Verdict.** Not now. The costs land on the two things Heather has made
load-bearing (evaluation and export), and the benefit (funext) has
workarounds that are already paid for. It goes on record as
[[interval-paths-for-funext]], so that the next round that hits "needs
funext" finds the trade-off written down. A cheaper variant to weigh there:
an interval with `coe` restricted to strict motives, in the spirit of the
UIP-free `transp` that `docs/sprop-design.md` keeps open. It gives no funext
but costs no canonicity.

### 2.3 Univalence

`iso` is rejected outright. Heather's data-representation story is
refinement (`issues/datarepr-separation.md`, the CoqEAL line), and the paper
makes the same point on p. 14: transporting `Nat_Bin → Nat_Bin` to `Nat →
Nat` along a univalence path keeps neither the complexity nor the
eliminator's definitional equations. Its proposed fix, univalent
parametricity (Tabareau, Tanter and Sozeau), is a white-box translation,
which is what a refinement framework is.

## 3. Quotients, conditions and h-levels

- **Constructors with conditions, without the interval.** Conditions on
  ordinary arguments (`pos 0 ⇒ neg 0`) are a quotient by a terminating,
  confluent rewrite with normal forms as the carrier. Functions out of the
  type are checked to respect the conditions definitionally. This needs no
  interval and no h-levels. It cannot be done in Heather's elaborator alone:
  if `neg` is a smart constructor, `match` on `neg(n)` at a neutral `n` stops
  reducing, because the smart constructor is stuck on `n` and is no longer a
  constructor. Arend keeps `neg n` a constructor and fires its condition only
  at canonical arguments. Heather avoided the need for `Int` by choosing the
  Lean encoding (`issues/std-int-encoding.md`), but polynomials without
  trailing zeros and finite multisets (Arend's `QPoly`, `PermSet`, p. 48)
  are quotient-shaped clients that will come. Filed as
  [[constructor-conditions]] with that caveat: it is a kernel former and
  waits for a client.
- **Setoids.** The paper calls them "rather impractical" (p. 12) because of
  the custom rewriting they require. Heather's paused setoid area agrees on
  the cost. Its explicit lifting and certificate reuse are a reasonable
  answer within a theory without quotients, and conditions would be the
  route out for the quotients that have normal forms.
- **Impredicative `\Prop` and level placement.** In conflict with Heather.
  Predicativity is decided, and placing a type in a universe by a proof of
  its h-level is classification of types by declaration, which
  `docs/sprop-design.md` rules out ("irrelevance is a property of fixed
  formers, not a classification of types").
- **h-prop elimination and unique choice.** Arend eliminates
  `nonempty(A)` into any `B` with a *proof* that `B` is a proposition,
  computing `f̄(in a) ≡ f(a)` (p. 8). Heather's `Squash` cannot do this:
  `Squash` is strict, so `squash a ≡ squash a'`, and a computing eliminator
  would give `f a ≡ f a'` definitionally from a propositional proof. That
  conversion is undecidable, and inconsistent with the model. Arend's
  `nonempty` is a HIT with a path constructor, and that is the reason it can
  compute. Heather's route to the specific property instead of choice is the
  `math-specific-choice` milestone.
- **Property fields.** Arend ignores property fields when it compares
  records, so for example `(C^op)^op ≡ C` for categories (p. 10). Heather's
  equivalent is a law field typed by `sEq`, which already compares
  irrelevantly through Σ-η. But `sEq` has had no eliminator since `transp`
  was removed, so such a law cannot rewrite a relevant goal. Making `Id`
  fields irrelevant would derive UIP. No action. A category library that
  wants `op` involutive definitionally should state its laws so that they
  are used only through other strict propositions, or live without it.

## 4. Records and classes (pp. 10, 14–15, 29–31)

- **Partial implementations (adopt).** `PseudoRing extends PseudoSemiring,
  AbGroup` implements `zero_*-left` from additive inverses, so no ring
  instance proves it again. Heather's `class Ring extends Semiring,
  GroupRel` has an empty body (`lib/std/algebra/semiring.hthr:143`), and `Int`,
  `Rat`, `CReal` and `Dyadic` each supply `zero_mul := …, mul_zero := …`
  with their own per-type theorem (`semiring.hthr:305`, `rat.hthr:1461`,
  `creal.hthr:1616`, `float/dyadic.hthr:283`). Arend's `\default` pairs
  (`func-Join` and `func-Join>=`, either implementable from the other,
  p. 38) are the same feature for interderivable laws. Heather has record
  field defaults already (`crates/elab/src/constructor.rs`,
  `elab_field_default`), checked hygienically at the construction. The
  missing piece is a child class giving a default for an *inherited* field
  that refers to the instance's other fields. Filed as
  [[class-inherited-field-implementations]], milestone `math-classes`
  ("clients use without restating laws").
- **Anonymous extensions** (`Semiring { E ⇒ Nat }`) turn fields into
  parameters on the fly. Heather's classes are already parameterised by
  carrier and operations (`Semiring<A>(same, add, mul)`), which covers the
  common use. No action.
- **Subsumptive subtyping and field overriding** (`GroupHom` overriding
  `Dom : Monoid` to `Group`) need kernel subtyping. Heather flattens and
  upcasts by projection (`docs/traits-design.md` §4,
  `docs/traits-named-upcast-design.md`). No action.
- **Dynamic blocks** (an implicit `\this` for definitions inside a class)
  correspond to Heather's receiver methods and `T::f` members, which Minus
  prefers anyway. `\classifying` fields correspond to instance keys. No
  action.
- **Level inference.** Arend removed its `\plevels`/`\levels` declarations,
  and a definition like `NatTrans` that once needed four explicitly ordered
  levels "turned out unnecessary altogether" under inference (p. 37). That
  is evidence for `implicit-level-polymorphism`'s "90% automation" claim.
  Logged there. It does not change that issue's blockers: level
  quantification is layer m in DeLaM.

## 5. Arrays (pp. 10–11, 15–16, 31)

Arend's `Array` exists for two reasons: definitional componentwise equality,
and nested recursion such as `Term F a` with children `Array (Term F a) (a
f)`, where the ih must be a function over `Fin`. Heather's `Vec^l(T; k)`
reduces to iterated Σ ending in `Unit`, so componentwise conversion is Σ-η,
and `Wf` children are a `Vec` with a transient ih over `Fin n`
(`crates/kernel/DESIGN.md`, the `Wf` paragraph). `DVec` is `DArray`. What
Heather lacks is Arend's rule for *functions* on `Fin (n+2)`: two of them
convert when they agree pointwise. That is sum-η at a function's domain, and
it is sound in the groupoid model because `Fin n` is discrete. It is worth a
kernel arm only if a client represents matrices or tensors as functions out
of `Fin` and wants `refl` proofs about them. `ml-tensor-shapes` should
decide that, so it is noted here rather than filed.

## 6. Tooling (pp. 4–5, 32–36)

- **The CLI is built for agents** (§5). `arend` checks a library, a module or
  one definition, prints errors and remaining goals, and offers retrieval:
  symbol search (`-ss`), proof search by statement pattern with `_`
  wildcards and infix (`-ps "_ + _ = _ + _"`), find usages (`-fu`), class
  hierarchy with `\new` and `\instance` sites (`-ch`), and scope at a
  definition (`-sc`), all with `--json`. It also prints elaborated
  definitions (`-p`), checks core terms (`-c`), and runs as a daemon that
  keeps the checked library in memory (`-d`). Heather's
  `ai-facing-tooling` and `lemma-selection-and-search` own the same
  direction, and `--only`/`--cache` already give single-declaration checks
  over a replayed prefix. Arend's experience is that retrieval comes first:
  the agent's bottleneck is finding the lemma, not checking it. Logged on
  `lemma-selection-and-search` with the recommendation to start with
  symbol and pattern search over module images.
- **Skills** (`sxhya/arend-skills`): `arend-formalize` (statement to a
  type-checking file with only `{?}` goals left), `arend-prove` (filling
  goals, with a catalogue of metas, decision tables and failure modes),
  `arend-quirks` (where the language differs from Rocq, Agda and Lean), and
  two error-diagnosis skills for messages that point at the wrong place.
  Heather's equivalent knowledge is spread over `CLAUDE.md`, project memory
  and issue files. Filed as [[agent-skills-pack]].
- **IDE actions worth having as CLI forms**: replace a tactic with the term
  it produced, replace an expression by its whnf, generate a function from a
  goal (with the minimal context), and an instance skeleton listing the
  unimplemented inherited fields. The first and last fit
  `ai-facing-tooling`. They are noted there, not filed separately.

## 7. The library (§6)

- **Locales.** `Locale extends CompleteLattice, HeytingAlgebra, Site`, with
  `Join : (E → \Prop) → E`. Arbitrary joins over subsets are small only
  because `\Prop` is impredicative, so Heather cannot copy the definition.
  The construction route is portable, though: preorder sites, and
  `SiteLocale P` as the reflection of a site into locales, are how
  `arend-lib` builds the locale of reals and the spectra of rings
  "by generators and relations" (p. 40). That is the formal-topology
  starting point `frame-and-locale-foundations` already asks for. Logged
  there, with schemes as locally ringed locales (and affineness stated
  intrinsically rather than through the spectrum) as the long-range
  customer.
- **Reals.** Isaev's cover spaces (arXiv:2412.20835) complete `Q` by Cauchy
  filters to the Dedekind reals and relate cover maps `R → R` to locale
  morphisms. They are a point-set alternative to localic completion that
  keeps Heine–Borel in the form "every Cauchy cover has a finite subcover".
  This is relevant to `math-reals` alongside Heather's regular Cauchy reals.
  Logged on `frame-and-locale-foundations`, whose localic reals it bears on.
- **Constructive algebra.** Domains via a tight apartness, PIDs as Bézout
  domains with the weak Noetherian property (every ascending chain of
  finitely generated ideals stabilises), Noetherian rings via bar induction,
  Smith domains and the Kaplansky condition, Richman's FTA without choice,
  algebraic closure of countable discrete fields. These are design
  precedents for the mathematics area's class hierarchy beyond ordered
  fields: definitions that are classically equivalent but constructively
  distinct, picked for which one is provable. `TFAE` chains are a small
  library convenience Heather's `calc` does not cover.
- **Solvers** for semigroups up to rings and Boolean rings, linear
  arithmetic over ordered rings, and composites in a category. Heather's
  tactics area already covers the ring and linear-arithmetic part.

## 8. Follow-up

Filed:

- [[class-inherited-field-implementations]] (`language`, `math-classes`):
  a child class implements inherited fields from its other fields, plus
  interderivable default pairs.
- [[agent-skills-pack]] (`infrastructure`): formalize, prove, quirks and
  error-diagnosis skills for agents working in Heather.
- [[interval-paths-for-funext]] (`kernel`, research): the trade-off in §2,
  waiting for a puller.
- [[constructor-conditions]] (`kernel`, research): quotients with normal
  forms as constructors with conditions, waiting for a client.

Logged on existing issues: `lemma-selection-and-search` (§6),
`implicit-level-polymorphism` (§4), `frame-and-locale-foundations` (§7).
