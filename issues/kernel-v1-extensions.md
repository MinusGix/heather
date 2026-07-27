---
title: Extend the kernel with Id and a small fixed former set
status: open
labels: [kernel,delam,design]
created: 2026-07-23
updated: 2026-07-26
---

DeLaM's object language is deliberately minimal: Nat, Π, universes, plus the
box/meta layer. No identity type, no Σ/sums — those were never in the paper
(checked ch. 04/06 directly). Any usable Heather needs them, so they are our
extensions beyond both the paper and the in-progress Coq formalization.

**Decision: extend with a small *fixed* former set; no general inductive
declarations in the kernel.** Each new former pays a bounded, known tax —
syntax (`term.rs`), the three substitution operations, typing, reduction +
conversion rules, code-recursor branches with their β rules (`rec.rs`
telescopes), budget-bounded `Debug`, tests — and each is a discrete,
auditable divergence from the formalization (per the [[kernel-v0-scope]]
policy). General user-declared inductives would instead put a datatype-
*declaration* syntax class into the code type and recursor (recursing over
declarations; logical relations over arbitrary strictly positive types in a
layered setting) — research-grade, and quite possibly never worth it: fixed
formers + encodings + front-end sugar cover the language for a fraction of
the trusted-base cost.

Candidate v1 set (order roughly = implementation order):

1. **Id + refl + J** — non-negotiable for stating `equiv` as a theorem
   object. J (not transport-only): standard, and the LR cases for Id/J are
   well-trodden MLTT territory.
2. **Σ + pair + fst/snd** (or dependent elim) — needed the moment IR nodes
   carry more than one field without Church-pair pain.
3. **Binary sums + case** — IR instruction alternatives.
4. **Unit, Empty** — cheap, useful (Empty gives negation; Unit gives
   degenerate cases).
5. **W-types: promoted from "deferred" to planned (2026-07-23).** The
   project goal is unification of programming *and mathematics*; something
   concrete now wants them: general well-founded recursion (`Acc`), which is
   the one thing the finitary-encoding story (Nat-approximants via large
   elim, fording via Id+Σ+sums) provably cannot reach — `Acc.intro` puts a
   function under the constructor, so no uniform depth bound exists. Plain W
   + Id (+ funext, which the user accepts as an axiom — see log) yields
   indexed W-types and hence `Acc`/inductive families by the standard
   indexed-containers reduction. Note the classic "W-encodings of *first-
   order* inductives need funext" complaint is irrelevant here: first-order
   data stays on the finitary encodings; W is for the infinitely-branching
   tier only.

**Earmarked metatheory check (for the formalization): Id/Σ at □ types.**
Ch. 06 checks `box t ≈ box t'` by converting the insides (~l. 527/535),
while the code recursor is intensional (stuck only on neutrals / boxed
globals). Adding Id makes code conversion *propositionally observable* at
`□(Δ ⊢ T)`; the recursor cases of the ch. 07 logical relations are where
this could bite. Nothing is expected to break, but this is the one
non-mechanical spot.

Σ (as landed) sharpens the same spot in two ways: (i) η-for-pairs is a
*definitional* equation the logical relations must respect at Σ-typed code —
the LR at `□(Δ ⊢ Σ … @ l)` has to be closed under surjective pairing, not
just structural on `pair`; and (ii) `fst`/`snd` are new neutral heads, so
the recursor's neutral cases (and the `tm_fst`/`tm_snd` β-branches) join
`elim_Nat`/`J` as things the fundamental theorem must cover. Still expected
to go through — η at a negative type is standard — but it is the concrete
form the "could bite" worry takes now, and worth checking before adding
sums (whose eliminator is *positive*, a different LR shape again).

Sums (as landed) are that different shape, and the *first positive*
eliminator among the extensions (Nat aside): the LR at `□(Δ ⊢ A + B @ l)` is
not η/projection-based like Σ but must instead be closed under the two
injections and `case`'s commuting conversions — the fundamental theorem's
`case` arm has to reduce a `case` on each canonical `inl`/`inr` and stay
neutral on a neutral scrutinee, with `tm_inl`/`tm_inr`/`tm_case` joining the
recursor's constructor/neutral cases. Concretely distinct from the Σ worry
(positive vs. negative), so it wants its own line in the ch. 07 check rather
than folding under surjective pairing; still expected to go through (positive
elimination is standard MLTT), but it is a separate obligation. The widest
telescope (`tm_case`: 3 univs, 7 globals, 6 recursive calls) is also the
most error-prone transcription — cross-checked in-kernel three ways
(identity-recursor typing, const-motive recursor, direct `tm_case` β test),
but that is decidability/soundness of *checking*, not the LR itself.

**Not a blocker for [[end-to-end-compile-instance]]:** universe
polymorphism makes Leibniz equality (`Eq A x y := Π(P : A → Ty l'). P x →
P y`) definable in the *current* grammar — transport free, sym/trans/cong
derivable, only J missing — and a toy IR can be Church-encoded with
`simulate` as its fold. Since each Compile instance carries a *concrete*
IR value, `simulate ir` reduces away and equiv proofs are Nat-induction;
no dependent elimination needed. The milestone can proceed on encodings
while this issue lands real formers; it should get *easier*, not blocked.

Interaction with [[box-synthesis-gap]]: new formers must respect the
checking-descent story — eliminators should stay inferable (annotated like
`App`/the recursors), intros checkable, so the meta-ANF invariant is
unaffected.

**W implementation earmarks** (for whoever lands it):

- β puts the recursive call **under a binder**: `elim_W (sup a f) ⇝
  s[a, f, λb. elim_W … (f b)]` — first β rule whose right-hand side
  synthesizes a λ around the recursive call. Reduction, the `tm_elim_w`
  recursor branch, and the subst depth bookkeeping all need this new shape;
  none of the 33 existing branches have it.
- Conversion: positive like sums — `sup` compared structurally at
  `Type::W`, `elim_W` neutral on a neutral scrutinee, **no η**.
- LR obligation (ch. 07 earmark): heaviest yet — positive *and* infinitely
  branching; the `sup` case quantifies over all subtree functions, in the
  layered/□ setting. Wants its own line next to the Σ (negative/η) and sum
  (positive/finitary) earmarks above.
- Funext-interaction earmark: funext (as an axiom) is purely propositional
  and □-conversion is syntactic, so it cannot leak into code equality —
  *provided* no rule ever derives □-level equality from function-level
  `Id`. Keep it that way: no "unbox congruence" for propositional equality,
  ever. Two functions may be propositionally equal yet distinguishable as
  code; that is a feature (the user's stated position), not a bug.

## Log

- 2026-07-23: Id landed: Type::Id + TmId encoding (El decode rule), refl, PM-based J (motive binds y,p; case closed; β J…refl ⇝ c). Threaded through subst (J motive dep(0,0,2)), typing, reduction, conversion (Id/TmId congruence, J neutral arm mirroring ElimNat), and the code recursors: four new branches ty_id/tm_id/tm_refl/tm_j (17 total), tm_j telescope modeled on tm_elim_nat (univs 2, globals 7, locals 6). All five transcriptions updated (rec.rs, subst depths, reduce β, BRANCH_DIMS, identity_branches x2, gen_branches); identity-recursor tests cross-check the new telescopes end-to-end. Generators (well-scoped + well-typed) now emit Id forms; golden tests for typing/reduction/conversion added. DESIGN.md fragment note updated. Next in the set: Σ.
- 2026-07-23: Σ landed: Type::Sigma + TmSigma encoding (El decode `El (Σ …) ⇝ Σ (El …)`, mirroring Π), intro `pair` (fully annotated, synthesizes), and **projections `fst`/`snd`** (not split) with β `fst (pair a b) ⇝ a` / `snd … ⇝ b`. Design decision resolved consciously against ch. 06: **projections + η-for-pairs**, because `tm_nf` is type-directed — a `Type::Sigma` arm comparing `fst a ≈ fst b` / `snd a ≈ snd b` mirrors the Π η arm exactly and gives definitional surjective pairing; a match/split eliminator is not η-compatible and would diverge from Π. `fst`/`snd` are neutral on a neutral pair, compared structurally (App-like) at neutral result types. Threaded through subst (Sigma cod / pair snd_ty / fst-snd snd_ty at dep(0,0,1)), typing, reduction, conversion (Sigma/TmSigma congruence, Σ-η, fst/snd neutral arms), and the code recursors: five new branches ty_sigma/tm_sigma/tm_pair/tm_fst/tm_snd (22 total; ty_sigma≡ty_pi shape, tm_sigma≡tm_pi, tm_pair≡tm_app dims dep(2,5,4), tm_fst/tm_snd dep(2,4,3)). All transcriptions updated (rec.rs, subst depths, reduce β, BRANCH_DIMS, identity_branches x2, gen_branches); identity-recursor tests cross-check the new telescopes end-to-end. Generators emit Σ forms; golden tests for typing/reduction/conversion added. DESIGN.md updated. Next in the set: binary sums + case.
- 2026-07-23: Binary sums + case landed (item 3, completing the v1 set 1–4).
  `Type::Sum` + `TmSum` encoding (`El (s + t) ⇝ El s + El t`, mirroring Π/Σ),
  intros `inl`/`inr` (fully annotated, synthesize), and a **dependent**
  eliminator `case^{l,l',l''}(z. M; A; B; x. c_l; y. c_r; t)` with β
  `case (inl a) ⇝ c_l[a/x]` / `case (inr b) ⇝ c_r[b/y]`. Design resolved as
  the **positive** dual of Σ: no η — `case` is neutral on a neutral scrutinee
  (like `elim_Nat`), and `tm_nf` at `Type::Sum` matches the two constructors
  like `Zero`/`Succ` at `Nat` (compare the injected value; tag mismatch =
  `NotConvertible`). The former is **non-dependent** (both summands in Γ), so
  `Sum`/`TmSum`/`ty_sum`/`tm_sum` drop the Σ binder extension. Threaded
  through subst (Case motive/branches at dep(0,0,1); sum branch depths
  ty_sum/tm_sum dep(2,3,2), tm_inl/tm_inr dep(2,4,3), tm_case dep(3,7,6)),
  typing, reduction (decode + Case β + is_whnf/is_neutral + fire_ty/tm_code
  arms), conversion (Sum/TmSum congruence + guards, positive Type::Sum arm,
  Case neutral congruence), and the code recursors: five new branches
  ty_sum/tm_sum/tm_inl/tm_inr/tm_case (**33 total**), `tm_case` the widest
  telescope yet (3 univs, 7 globals, 6 recursive calls; U_M over (g,z:A+B),
  u_l/u_r over (g,x:A)/(g,y:B) with U_M^{id,inl x/z}/U_M^{id,inr y/z}). All
  transcriptions updated (rec.rs branch_terms/branch_specs, subst depths,
  reduce β, BRANCH_DIMS 33, identity_branches ×2, gen_branches, count_term,
  the conv/reduce/typing dummy-branch literals, conv_pair_properties'
  build-array + decode/mutate_encoding); the identity-recursor typing tests
  and the const-motive recursor cross-check the new telescopes end-to-end.
  Generators (well-scoped + well-typed) emit Sum/Inl/Inr/Case; golden tests
  for typing/reduction (β for all five recursor branches, incl. tm_case) /
  conversion added. DESIGN.md fourth-extension paragraph added.
- 2026-07-23: 2026-07-23: Unit + Empty landed (item 4 of the set, ahead of sums). Unit: Type::Unit + TmUnit encoding (El decode El Unit ⇝ Unit), single intro Triv (⟨⟩), and **definitional η / proof irrelevance** — a Type::Unit arm in tm_nf accepts any two terms at Unit type, mirroring the Σ-η decision (type-directed, no eliminator, no new neutral head). Empty: Type::Empty + TmEmpty encoding (El Empty ⇝ Empty), no intro, dependent eliminator elim_Empty^l(x.M; t) : M[t/x] modeled on elim_Nat minus base/step — no β rule (no constructors), neutral on a neutral scrutinee, fully annotated so it infers. Threaded through subst (ElimEmpty motive dep(0,0,1)), typing, reduction (decode + ElimEmpty congruence, is_whnf/is_neutral), conversion (Unit/Empty type congruence, Unit-η arm, Empty via tm_nee, TmUnit/TmEmpty congruence at Ty, ElimEmpty neutral arm), and the code recursors: six new branches ty_unit/ty_empty/tm_unit/tm_empty/tm_triv/tm_elim_empty (28 total; nullary ones mirror ty_nat/tm_nat/tm_zero, tm_elim_empty mirrors tm_elim_nat dep(1,3,2)). All transcriptions updated (rec.rs, subst depths, reduce β, BRANCH_DIMS, identity_branches x2, gen_branches); identity-recursor tests cross-check the new telescopes end-to-end. Generators (well-scoped + well-typed) emit Unit/Empty forms; golden tests for typing/reduction/conversion added. DESIGN.md updated. Next in the set: binary sums + case (item 3, still pending).
- 2026-07-23: W-types landed (item 5, closing the planned former set). Type::W (shape/pos, pos binds one; ≡ Σ/Π shape) + TmW encoding (El (W s t) ⇝ W (El s) (El t)), intro sup(x:S.T; a; f) with f : Π(y:T[a/x]). W (fully annotated, synthesizes), dependent eliminator elim_W^{l,l',l''}(x:S.T; z.M; a f ih. s; t) with step binding (a, f : Π(y:T[a/x]).W, ih : Π(y:T[a/x]).M[f y/z]). Positive like sums: no η, neutral on neutral scrutinee, Type::W conversion compares sup label + subtree function. The novel bit: β synthesizes a λ — elim_W (sup a f) ⇝ s[a, f, (λy. elim_W …(f y))/ih] — the first RHS that builds a binder around the recursive call; reduce.rs constructs it from the eliminator's annotations (shift-under-binder via a closed-placeholder template destructure, same trick as typing's sup(a,f) construction). Threaded through subst (W/TmW pos dep(0,0,1), ElimW motive dep(0,0,1) step dep(0,0,3)), typing, reduction (decode + β + congruence + whnf/neutral), conversion (W/TmW congruence, positive Type::W arm, ElimW neutral arm with the full (a,f,ih) step telescope), and the code recursors: four new branches ty_w/tm_w/tm_sup/tm_elim_w (37 total; ty_w≡ty_pi dep(2,3,2), tm_w≡tm_pi, tm_sup≡tm_pair dep(2,5,4), tm_elim_w dep(3,6,5) — nests Π types inside its global bindings, deepest binding-type construction yet). All transcriptions updated (rec.rs branch_terms/branch_specs, subst depths, reduce β, BRANCH_DIMS 37, identity_branches ×2, gen_branches, count_term/count_branches — also fixed count_branches' pre-existing omission of the five sum branches, dummy-branch literals, conv_pair_properties 37-arrays + decode/mutate_encoding + gen_encoding TmW arm). Generators (well-scoped + well-typed) emit W/TmW/Sup/ElimW (wt: sup intro at Type::W, elim_W with constant motive); golden tests for typing (formation/intro/encoding/elim incl. binder-type checks)/reduction (decode, direct β incl. exact synthesized-ih term, recursor β for all four branches)/conversion (congruence, positive sup, elim_W neutral) added; identity-recursor + const-motive recursor cross-check the telescopes end-to-end. DESIGN.md fifth-extension paragraph added. scripts/test fully green.
- 2026-07-24: Metatheory earmark discharged: [[metatheory-ch07-pass]] closed — all six formers clear the ch. 07 logical relations, no rule changes (docs/metatheory-ch07-extensions.md). Remaining debt from this issue is documentation, not metatheory: [[delam-extensions-writeup]] for the declarative ch. 04 rules.
- 2026-07-24: Premise correction (2026-07-24): item 5's reassurance that the classic 'W-encodings of first-order inductives need funext' complaint is irrelevant because 'first-order data stays on the finitary encodings' is FALSE. The finitary/fording encodings reach the linear fragment only -- at most one recursive field per constructor (List, Bits) -- because elim_Nat recurses on a predecessor, and a constructor with two recursive fields needs the family at two indices that are not the predecessor; every route to that puts the child behind a function of a measure, which is stuck at a neutral measure, so the constructor is not in constructor form and match on it stops reducing. Branching first-order data (Node(Tree,Tree), and the IR expression knot) therefore lands on W + funext unless the kernel grows a former. Consequence for this issue: W is no longer 'for the infinitely-branching tier only', and the funext earmark's blast radius is a live decision rather than a settled containment. See docs/inductive-tier1-lowering.md 8.1, docs/branching-inductives-choice.md, issues/tier1-branching-constructors.md. One candidate is a new positive former (Wf: arity-Nat shapes with Sigma-tuple children, so Sigma-eta/Unit-eta replace funext) sized at roughly the W landing: 4 code-recursor branches plus a ch. 07 pass, with an easier LR obligation than W's since it is finitary and tuple-shaped.
- 2026-07-25: 2026-07-25: Correction to the W-types promotion note: the 'first-order data stays on the finitary encodings' reassurance was false — the finitary encodings reach only the linear fragment (docs/branching-inductives-choice.md §1). Resolution: the Wf former (finitary branching, Sigma-tuple children) joins the former set for all first-order data ([[wf-former]], docs/wf-former-design.md); W + funext stay as the infinitary tier (Acc) as originally intended.
- 2026-07-26: Refinement to the W-types entry's funext claim (item 5): 'plain W + Id (+ funext...) yields indexed W-types and hence Acc' overstates what funext is for. Acc IS now built by the standard indexed-container reduction (docs/acc-via-w.md, crates/kernel/tests/acc.rs) with Psi EMPTY -- no funext, no new axiom. Defining Acc, introducing it, recursing over it and computing with it are all definitional; funext is needed only for the direction nothing yet needs, proving Acc(a) a proposition (and so that wfrec does not depend on which accessibility proof it is given). The axiom is therefore not a cost of reaching tier 2; it is a cost of reasoning ABOUT tier-2 proofs. Same correction applies to docs/branching-inductives-choice.md §1's 'funext arrives as an axiom anyway for tier 2', which was one of the points weighed in the route A/C decision -- it did not change that outcome (route C was chosen on beta-on-open-children, which W fails regardless) but the ledger should be accurate.
