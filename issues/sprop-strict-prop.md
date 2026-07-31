---
title: "SProp: a definitionally irrelevant sort with strict equality"
status: open
labels: [kernel,delam,design,metatheory]
created: 2026-07-28
updated: 2026-07-31
---

Decision (2026-07-28, discussion): Heather gets an SProp — a definitionally
proof-irrelevant sort with a strict equality — promoted from the standing
"later" foundations position by [[indexed-families]] route 2b, which needs an
irrelevant index equation for fording to pass the setoid test. This issue
owns the design decisions and the kernel round. The user's position on proof
relevance stands: relevance is the default ontology and `Id` stays the
surface `=`; SProp is opt-in squashing for evidence that should be invisible
(index constraints, guard predicates, side conditions), and `sEq` stays
mostly generator-internal.

## What it assumes from elsewhere

- **[[indexed-families]]** owns route 2b and the acceptance bar for the
  general indexed-family scheme. Assumed here: only that 2b is the promoting
  customer; if 2b dies, this issue's independent benefits (proofs riding in
  data stop taxing value equality) get re-weighed, not inherited.
- **[[kernel-v1-extensions]]** owns the □-observability earmark (Id made
  code conversion propositionally observable). Assumed here: that earmark is
  the right place to check `sEq`'s sharpening of it.

## Why this system is unusually well-positioned

Recorded so the risk assessment is not re-derived:

- **Predicativity is already decided** (2026-07-23; impredicative Prop
  rejected), and the known catastrophe — normalization failure with
  proof-irrelevant propositional equality (Abel–Coquand) — lives in the
  *impredicative* combination.
- **Boxed code compares syntactically** (`crates/kernel/src/conv.rs:30`
  @ 0f3e24b), so term-level irrelevance cannot reach □-equality — the same
  firewall that contains funext. Two proofs definitionally equal yet
  distinguishable as code is the intended semantics, not a leak.
- **The kernel already ships a miniature**: `Unit`'s proof-irrelevance arm
  (`conv.rs:789` @ 0f3e24b) is exactly an "accept any two terms at this
  type" case in `tm_nf`, coexisting with the code layer, through a ch. 07
  round. SProp generalizes an audited pattern, not a new kind of rule.

Reference point: Gilbert–Cockx–Sozeau–Tabareau, *Definitional
Proof-Irrelevance without K* — the unlayered version of most of what
follows.

## Decisions to make

1. **Sort structure — settled 2026-07-28, and the sort dissolves.** Spelled
   in `docs/sprop-design.md` §1: the kernel gets **no third sort** —
   propositions are ordinary `Typ` formers with per-former irrelevance arms
   (the audited `Unit` pattern), and `SProp` survives only as an elaborator
   classification. Grounds: ch. 04's grammar is two-sorted with all layered
   machinery threaded per-sort (a third sort multiplies the recursor's
   motive/branch vectors, contextual types, global binders); the 2b
   customer needs `sEq` *inside* relevant Σ-payloads anyway, so a separate
   sort would need a mandatory embedding door; and per-former arms cannot
   leak — "no cumulativity into `Ty`" reframes as "the irrelevant-former
   set is closed and enumerated in the design doc." The closure rules
   (`Π` from `Ty` into props lands in props) hold as *theorems* of the
   existing η arms, not as rules — same move as `Wf` storing children
   where η already reaches. No `SProp^l` hierarchy to design: `sEq^l` sits
   in the one hierarchy that exists; predicativity is inherited. Agda's
   `Prop ℓ` precedent moot.
2. **`transp` — the eliminator, corrected 2026-07-28.** What 2b needs is
   not OTT-style cast between types but transport along a term-level `sEq`
   through a motive: `transp^{l,l'}(I; x.P; a; b; e; t) : P[b]` — J's
   non-dependent cousin, fully annotated so it synthesizes. The first
   filing said this "punctures the reduce/conv separation"; **it does
   not** — the rule decomposes into three pieces, each landing where the
   kernel already puts that kind of equation:
   - `reduce.rs`: ordinary β on the intro form only —
     `transp(…; srefl; t) ⇝ t`. Sufficient for closed computation by
     canonicity (a closed `sEq` proof normalizes to `srefl`); no
     conversion query in reduction, same shape as J's β.
   - `conv.rs` `tm_nf`: the **strip rule**, the load-bearing novelty —
     on a whnf'd transp head, a *guarded* query `a ≡ b`; success strips
     to `t`. Covers neutral proofs at convertible endpoints
     (`plus(0,n) ≡ n`, `n` open), which is what makes casts invisible on
     open data. Joins the η family (Π-η, Σ-η, Unit irrelevance): type-
     directed equations beyond β already live here. The new *shape* is
     the guard: the first conv query whose failure means "take the
     neutral path", not "not convertible". **Settled 2026-07-28**
     against `Conv`'s actual state (@ 0f3e24b) — the feared surprises
     dissolve like the punctures claim did:
     - *Catch `NotConvertible`; propagate `OutOfFuel`.* Those two are
       the whole error enum (conv.rs:69). Exhaustion is global — the
       shared budget is at 0 and every later `spend()` fails anyway —
       and swallowing it would make the verdict depend on *where* the
       budget died.
     - *No fuel refund.* `Conv { fuel: u64 }` is the entire mutable
       state (conv.rs:240), and monotone-decreasing fuel is the
       totality argument (conv.rs:41–45); a refund needs a subtler
       termination measure and buys nothing — the failed query's
       spend is real work, and budget-sensitivity of the verdict is
       inherent to fuel-bounded checking.
     - *No backtracking hygiene.* A successful strip rewrites by a
       proven equation (`P[a] ≡ P[b]`), not a choice point, so eager
       stripping never loses completeness; a failed guard has mutated
       nothing but fuel. No caches exist to dirty, and future
       memoization stays coherent because the guard is an *ordinary*
       query caught at the call site, not a new query mode — a
       memoized `NotConvertible` remains a true fact, only the
       caller's reaction differs. (Standing constraint for any future
       memo table, needed regardless of strip: never cache
       `OutOfFuel`.)
     - *Placement — the one real novelty found:* the η family is
       *type*-keyed (each rule is a `Type::…` arm of `tm_nf`), but
       strip is *term-head*-keyed — a stuck transp sits at any type
       `P[b]` — so it cannot be a type arm. It is a whnf-adjacent
       loop per side before type dispatch: whnf; if transp head and
       guard succeeds, replace by the payload and re-whnf. Each strip
       pays `spend()`, fitting the fuel doc's "one budget shared by
       all reduction steps and comparison nodes"; termination is the
       payload being a strict subterm. Guard query runs at the
       transp's own `I : l` annotations, left-biased, W-arm style.
       Fast path: syntactic `==` on the endpoints first.
   - `tm_ne`: congruence that **inverts J's discipline** — J compares
     its proof structurally (`conv.rs:1231` @ 0f3e24b, `tm_nee`) because
     the proof is the scrutinee; transp's stuckness is keyed on the
     endpoints, so its arm compares `I`, `P`, `a`, `b`, `t` typed and
     the proofs at `sEq` type, where the irrelevance arm accepts —
     one uniform principle, no relevance marks. Fixed formers mean this
     is one special arm, not machinery.
   Derived check, no extra rule needed: `Vec(D; transp(e,n)) ≡ Vec(D;n)`
   via structural neutral-`Vec` comparison of lengths as terms, where the
   strip fires. No `sJ`: transp + irrelevance derive it; UIP at `sEq` is
   definitional by construction. Flag for the ch. 07 round: `sEq(Ty l; …)`
   is an *irrelevant equality of codes* — a new observer next to the
   □-observability earmark; expected inert (stuck neutral, box conversion
   untouched) but it wants its own line.
3. **Inhabitants and elimination discipline.** Minimal initial set, former
   discipline: `sEq` (the customer) and `sEmpty` (eliminates anywhere);
   squash `∥·∥` later with its restricted eliminator. SProp inductives
   otherwise eliminate into SProp only.
4. **Code layer: SProp enters it** (decided 2026-07-28). The alternative —
   keeping the encodings opaque so metaprograms know-but-cannot-assert the
   fording structure — was considered and declined: encodings live in types
   metaprograms see, so `sEq`/`cast` get code formers. `rec.rs` bill: a
   handful of branches plus the usual five transcriptions. This sharpens the
   [[kernel-v1-extensions]] earmark: `sEq` adds a *definitionally*
   irrelevant observer where Id added a propositional one. Expected fine
   given syntactic box conversion; the ch. 07 round stares here.
5. **ch. 07.** The LR needs an irrelevance case — GCST did it unlayered;
   nobody has done it layered. Own round, wf-former discipline: rules doc
   first (`wf-former-design.md` style), abort criterion stated before code.

## Sequencing note

The postulate-in-Ψ de-risk pattern does not apply to the interesting part:
irrelevance is a *conversion* feature, and postulates validate a typing
interface but not a definitional equality (the same limit the `Wf` round
hit — its β laws were propositional until the former landed). So the
de-risk here is the rules doc plus the ch. 07 sketch, not a prototype.
Does not gate [[indexed-families]] route 1.

## Coupling: the NbE conversion round

**2026-07-31.** [[whnf-sharing-term-growth]]'s design
(`docs/nbe-conversion-design.md` §9) prices this issue's formers against the
TYPES 2024 negative result (NbE for CCobs needed a bespoke *irrelevant*
semantic domain, three designs tried). Verdict: the value-domain round does
**not** buy that problem back, because Heather compares weak-head values
type-directed and never normalizes — the three irrelevance arms (`Unit`,
`sEq`, `sEmpty`) still accept any two terms without inspecting them, and the
strip transplants with its re-whnf deleted. Nothing here needs changing.

The one thing that would change it is recorded as a shared invariant: **the
kernel has no normal-form readback, and adding one is an SProp design round,
not a convenience** — a readback is precisely what forces irrelevance into
the semantics.

## Log

- 2026-07-28: Filed, off the [[indexed-families]] 2b coupling and the
  decision (discussion, same day) to go for SProp.
- 2026-07-28: cast round of discussion: decision 2 rewritten as transp (motive transport along term-level sEq, not type cast). The 'punctures reduce/conv separation' claim from filing is withdrawn: beta-on-srefl in reduce + a guarded strip rule in tm_nf + endpoint-keyed congruence in tm_ne, each with in-kernel precedent (J's beta, the eta family, fixed-former special arms). Genuinely open: guard failure semantics/fuel/cache hygiene, sEq at Ty l for ch. 07, LR shape of the strip.
- 2026-07-28: Guard semantics settled against Conv's actual state (fuel-only, no caches; error enum is exactly OutOfFuel|NotConvertible): catch NC / propagate OutOfFuel, no fuel refund (monotone fuel IS the totality argument), no backtracking hygiene (strip is rewrite-by-equation, a failed guard mutates only fuel), future memoization stays coherent (ordinary query, call-site catch; never cache OutOfFuel). One genuine finding: strip is term-head-keyed unlike the type-keyed eta family, so it is a whnf-adjacent per-side loop in tm_nf before type dispatch, spend() per strip. Remaining open: sEq at Ty l (ch. 07 earmark), LR shape of the strip. Next: rules doc, sort-structure section first.
- 2026-07-28: Rules doc drafted: docs/sprop-design.md (wf-former-design.md style). Decision 1 settled and the sort dissolves: no third syntactic sort — propositions are Typ formers with per-former irrelevance arms (Unit pattern), SProp is elaborator classification only. Grounds: ch. 04 grammar is two-sorted with everything threaded per-sort; 2b needs sEq inside relevant Sigma-payloads anyway; per-former arms cannot leak, and Pi/Sigma-closure of irrelevance holds as theorems of the existing eta arms. Doc carries: former set (sEq mirroring Type::Id, sEmpty with Empty-reuse as the shed-weight alternative), transp rules, the settled guard semantics, rec.rs bill (45 -> 52), ch. 07 predicted shapes with abort criterion (revert to judgmental sort if the LR demands relevance marks), and 2b setoid acceptance. Next: doc review + rule freeze, then the ch. 07 sketch before any kernel code.
- 2026-07-28: Rules doc reviewed and frozen; ch. 07 sketch done as part III of docs/metatheory-ch07-extensions.md (secs 18-22). Two findings from working the LR cases, both folded back into the design doc: (1) the strip closure cannot be a per-type clause — transp(e;5) is a whnf at Nat that must relate to 5 — so the LR's evaluation notion becomes whnf-then-strip, the semantic counterpart of the algorithm's whnf-adjacent loop; first round to edit a shared notion rather than add cases. (2) The strip premise must be declarative convertibility (a ~=~ b : I), not semantic relatedness — the semantic version is circular by levels (motive at l', index type at arbitrary l); mirrors how neutrals already use generic equivalence. Sec 20 re-runs the Id round's box-observability argument and defuses its warning: irrelevance collapses proofs, not endpoints; endpoint checking still goes through conversion-at-box = syntactic ==. sEq(Ty l) argued inert. Pre-code verdict: abort criterion NOT triggered, no relevance marks anywhere. Standing risk carried to the with-code FT pass: the evaluation-notion edit touches every term-relation case and was checked for shape, not in full. Next: kernel round proper (design doc sec 8 step 3).
- 2026-07-28: Kernel round landed (design doc sec 8 steps 3-4): Type::SEq, Term::SRefl, Term::Transp across term/subst/typing/reduce/conv/fmt, gated out of layer c (not_code_layer reintroduced, Vec/Fin-style). Conversion carries the three designed behaviours: sEq irrelevance arm in tm_nf, the strip loop in Conv::tm's term-whnf stage with the settled guard semantics (catch NC, propagate OutOfFuel, no refund, spend per strip), and the endpoint-keyed transp congruence in tm_ne that skips proofs. Reduction has beta-on-srefl only. Tests: seq_transp.rs (14, four-axis discipline) all passing; full suite green; property generators extended. One finding the bench gate caught: the strip check must be an inline discriminant read in Conv::tm, not a whnf-wrapping helper — the helper's extra Term moves cost 1.35x on conv/computed-numeral; fixed, 81 bench comparisons back within thresholds. DESIGN.md entry added. Remaining: sEmpty (step 5, or the Empty-reuse shed), rec.rs code round, then the 2b setoid acceptance.
- 2026-07-28: sEmpty landed (design doc sec 8 step 5, former half): Type::SEmpty level-indexed, ElimSEmpty eliminating anywhere with no beta, irrelevance arm in tm_nf, scrutinee-skipping congruence in tm_ne, same not_code_layer gate. Empty itself untouched — the contrast (sEmpty hypotheses convertible, Empty neutrals structural) is pinned in seq_transp.rs so the declined Empty-reuse alternative cannot happen by drift. 17 tests green, full suite 43 binaries, bench gate clean. Remaining before acceptance: the rec.rs code round (TmSEq/TmSEmpty, 7 branches, five transcriptions, gate lift), then 2b setoid.
- 2026-07-28: rec.rs code round landed (design doc sec 8 step 5 complete): TmSEq/TmSEmpty codes with El decoding, seven recursor branches exactly as sec 6 billed (45 -> 52: ty_seq/tm_seq mirror the Id pair, the sEmpty trio mirrors Empty's, tm_srefl mirrors tm_refl, tm_transp is tm_j with a one-binder motive and the proof recursed as syntax), all five parallel transcriptions (subst deps, reduce fire arms, BRANCH_DIMS, both identity_branches, gen_branches), gate lifted. seq_codes.rs (6): El decoding, identity-recursor round-trips including a stuck transp as code in non-empty Delta (strip does not reach inside a box) and a poisoned-branch control — all first-run green, which is the telescopes agreeing with the fire wiring. Full suite 44 binaries. Bench: perturbed-pairs re-recorded (generator arm counts shifted the RNG corpus, not kernel cost; generator-free computed-numeral stayed at baseline). The kernel round is COMPLETE; remaining on the issue: 2b setoid acceptance (indexed-families prototype), ch. 07 full FT pass, sEq(Ty l) earmark.
- 2026-07-29: 2b setoid acceptance PASSED (design doc sec 8 step 6, the last step): crates/elab/tests/indexed_route_2b.rs, the indexed-families route-2b prototype, signs off — match beta definitional on open recursive data, value equality lemma-free (would-be transport lemma checks as refl), mismatched indices reject, all through the landed sEq/transp behaviours with no kernel change. What the round's three behaviours actually carry there, measured: the irrelevance arm plus Sigma-eta do the beta and value-equality work (every stored/re-derived proof meets conversion at sEq type); the strip carries value-level casts and transp-spelled lengths; the guard's fail-then-neutral path runs (and must fail harmlessly) inside every open-data beta comparison. One measured edge for the ch. 07 with-code FT pass: the strip is head-only (Conv::strip fires on a transp at the head of a compared term), so a stuck-but-strippable transp blocking an elimination spine is invisible — cast ~ payload holds while elim(cast) ~ elim(payload) does not, an algorithmic incompleteness vs the declarative strip+congruence closure, confined to redundant terms (a cast at convertible endpoints is never needed). Pinned as a negative in the prototype; the ch. 07 completeness statement should scope the strip's congruence closure explicitly rather than inherit the eager-strip completeness remark, and the 2b generator's rule is to never emit such casts. Remaining on this issue: ch. 07 full FT pass, sEq(Ty l) earmark.
- 2026-07-31: Coupling note added from the NbE conversion design round (docs/nbe-conversion-design.md sec 9, [[whnf-sharing-term-growth]]): the value-domain conversion round does NOT buy back the TYPES 2024 negative result. Their bespoke irrelevant semantic domain is forced by NORMALIZATION — a proof is evaluated and read back, so the domain must identify all proofs of an irrelevant type; Heather reduces to weak head form and compares type-directed, so the Unit/sEq/sEmpty arms still accept any two terms without inspecting either, the derived Pi/Sigma closure is the same recursion through the same eta arms, and Conv::strip transplants with its re-whnf deleted (endpoints and payload are already values). One structural improvement: the box firewall stops being disciplinary — a box value carries raw syntax with no environment, so there is nothing in which its payload could be evaluated. Recorded as a shared invariant in both this issue and docs/sprop-design.md sec 1: the kernel has no normal-form readback, and adding one (normalize API, diagnostics, cached normal forms) is an SProp design round with the TYPES 2024 bill attached, not a convenience. The head-only-strip gap from the 2b acceptance is neither widened nor narrowed — it is a property of where the strip is keyed, not of how reduction is implemented.
