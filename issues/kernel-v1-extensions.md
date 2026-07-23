---
title: Extend the kernel with Id and a small fixed former set
status: open
labels: [kernel,delam,design]
created: 2026-07-23
updated: 2026-07-23
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
5. W-types: deferred until something concretely wants them.

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

## Log

- 2026-07-23: Id landed: Type::Id + TmId encoding (El decode rule), refl, PM-based J (motive binds y,p; case closed; β J…refl ⇝ c). Threaded through subst (J motive dep(0,0,2)), typing, reduction, conversion (Id/TmId congruence, J neutral arm mirroring ElimNat), and the code recursors: four new branches ty_id/tm_id/tm_refl/tm_j (17 total), tm_j telescope modeled on tm_elim_nat (univs 2, globals 7, locals 6). All five transcriptions updated (rec.rs, subst depths, reduce β, BRANCH_DIMS, identity_branches x2, gen_branches); identity-recursor tests cross-check the new telescopes end-to-end. Generators (well-scoped + well-typed) now emit Id forms; golden tests for typing/reduction/conversion added. DESIGN.md fragment note updated. Next in the set: Σ.
- 2026-07-23: Σ landed: Type::Sigma + TmSigma encoding (El decode `El (Σ …) ⇝ Σ (El …)`, mirroring Π), intro `pair` (fully annotated, synthesizes), and **projections `fst`/`snd`** (not split) with β `fst (pair a b) ⇝ a` / `snd … ⇝ b`. Design decision resolved consciously against ch. 06: **projections + η-for-pairs**, because `tm_nf` is type-directed — a `Type::Sigma` arm comparing `fst a ≈ fst b` / `snd a ≈ snd b` mirrors the Π η arm exactly and gives definitional surjective pairing; a match/split eliminator is not η-compatible and would diverge from Π. `fst`/`snd` are neutral on a neutral pair, compared structurally (App-like) at neutral result types. Threaded through subst (Sigma cod / pair snd_ty / fst-snd snd_ty at dep(0,0,1)), typing, reduction, conversion (Sigma/TmSigma congruence, Σ-η, fst/snd neutral arms), and the code recursors: five new branches ty_sigma/tm_sigma/tm_pair/tm_fst/tm_snd (22 total; ty_sigma≡ty_pi shape, tm_sigma≡tm_pi, tm_pair≡tm_app dims dep(2,5,4), tm_fst/tm_snd dep(2,4,3)). All transcriptions updated (rec.rs, subst depths, reduce β, BRANCH_DIMS, identity_branches x2, gen_branches); identity-recursor tests cross-check the new telescopes end-to-end. Generators emit Σ forms; golden tests for typing/reduction/conversion added. DESIGN.md updated. Next in the set: binary sums + case.
