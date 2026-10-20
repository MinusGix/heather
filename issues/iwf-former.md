---
title: IWf: finitary inductive families as a former, with no stored index equation
status: open
labels: [kernel,design,delam,metatheory]
created: 2026-09-30
updated: 2026-10-20
---

Owns the `IWf` former round: `docs/iwf-former-design.md` (rule set
frozen 2026-10-13, not implemented). This is [[indexed-families]]'s route 4,
extended with an output-index function. It is Dybjer's finitary inductive
families in `Wf`'s shape:
- `IWf(I; x:S. n; x. o; x i. c)(m)`;
- `sup_i(a; cs) : IWf(…)(o[a])`;
- children in a dependent tuple `DVec(k; i. F)`.

## Why now

Route 2b stores an index equation in every value, and uses it through
`transp` with the strip. [[sprop-strip-normalization-open]] found two costs
the round had not priced:
- The strip is Werner's rule, open predicatively.
- A computing `transp` into relevant motives gives UIP for `Id`.

A constructor that *is* at its result index stores nothing, so neither
cost arises.

## What the design claims

The full argument is in the doc. Items marked checked have a Coq probe:
`../Lean/delam/probes/IwfProbe.v`.

- β fires on every constructor on open data, including at a computed
  result index. There is no form B. (checked)
- Value equality is equality of the shape and the children, with no
  proof component. Cross-spelling holds by conversion.
- Fording's F1–F3 rejections lift, because child indices are stored, not
  recomputed. (F2, F3 checked)
- `dnth` is derivable in the kernel's first-order style: a fixed family,
  with the motive quantifying over an embedding `Fin k → Fin n`. It
  reduces to projections on a neutral tuple. (checked)
- Inversion at a constructor-headed index is form A's motive device,
  kept. (checked on `vhead`)
- There is no negative premise, conversion premise or strip in
  reduction, and no stored proof.

## Status (doc §12, §13)

The rule set (doc §1–§6) is frozen, 2026-10-13. In the kernel, `DVec` and
`dnth` have landed (doc §13 step 2, 2026-10-17), gated to layers p and m;
`IWf`/`sup_i`/`elim_IWf` (step 3) and the codes (step 4) have not. The Coq formalization has checked the frozen rules (typing at
every layer but V, computation at D and M), with the code-recursor
branches derived there before `rec.rs` has them (heather-coq
`M17_DESIGN.md`; Log, 2026-10-16). What
is still open is the generator's and changes no typing or reduction rule:
inversion at parameterized or container index types (§12.1), mutual
families (§12.2) and migrating route 2b's declarations (§12.4).
§12.1 and §12.2 are checked in the formalization's rules at `List a`
and at `Σ(tag). Nat` (Log, 2026-10-20); a container index type and a
tag-dependent `I_tag` are not. An
independent review of `docs/no-uip-model.md` §4 is written
(`docs/no-uip-model-review.md`), and its three local fixes and four
missing steps are applied (§4.4a there). It backs the no-UIP claim and
does not gate the freeze (§12.3). `Vec`/`Wf` stay
separate formers now, with abbreviations as the target (§10).

## What it assumes from elsewhere

- **[[indexed-families]]** owns the route choice. Assumed here: only that
  route 4 was set aside for its cost, not for a defect.
- **[[sprop-strip-normalization-open]]** owns the findings about `transp`.
  Assumed here: only its two conclusions, UIP and the open normalization
  question.
- **[[wf-former]]** owns `Wf`/`Vec`/`Fin`. Assumed here: their rules as in
  `docs/wf-former-design.md`, which this former extends.

## Log

- 2026-09-30: Decided with the user: (1) `transp` and the strip are removed, with the argument in doc §7; `docs/sprop-design.md` carries a revision note. (2) The family level is `l ⊔ li`, forced by the codes (§1.2). (3) `match` ships tiers 1–2: form A's motive inversion, and index abstraction with no equations. Tier 3, unification without K with deletion only at index types with decidable equality (Hedberg-generated K), comes when an example needs it (§8.3). What remains open before freezing is §12: inversion at wider index types, mutual families, the no-UIP model argument, and migration.
- 2026-09-30: §12.3's no-UIP argument is written: `docs/no-uip-model.md`, on paper and not reviewed. It uses the groupoid model, with `Ty 0` as sets and bijections, so `Id^1(Ty 0; Bool; Bool) = {id, swap}` and `UIP₀` is empty. The strict propositions are unions of connected components of the context; that lemma is proved there. DeLaM's globals and `□` are interpreted in stages over sets of syntactic instantiations, which is argued rather than checked. The same model validates `transp` at strict motives and refutes a relevant `transp`, which confirms the §7 decision.
- 2026-09-30: The components lemma of `docs/no-uip-model.md` §3 is mechanized in `../Lean/delam/probes/NoUipComponents.v`, closed under the global context. Mechanized: strict propositions are transported along context morphisms, strictly stable under substitution, and definitionally irrelevant; `srefl`, `elim_sEmpty` and `ElimSquash`; `transp` at a strict motive exists. In the groupoid of types and bijections: no relevant `transp` (`no_relevant_transp`), and UIP at `Ty 0` fails (`no_uip0`). §4, DeLaM's globals and `□`, remains argued only.
- 2026-09-30: `docs/no-uip-model.md` §4 has been self-reviewed against the Coq formalization's declarative rules. It is right in outline, and three things were fixed. (1) `□`'s discreteness rests on Static Code, which is syntactic only up to level equivalence (`StaticCodeEq.v`), not on `conv.rs`. (2) The interpretation is now three explicit stages, with environments carrying syntax and semantics, plus the semantic global substitution lemma that validates `letbox`'s β. (3) The scope excludes postulated globals. Every layer fact used is a side condition of a cited rule. Still open: an independent review, and the substitution lemma written out case by case.
- 2026-09-30: `docs/no-uip-model.md` §4.2a writes out the semantic global substitution lemma, `⟦t⦃σ⦄⟧ρ ≃ ⟦t⟧(ρ·σ)` for every global substitution `σ`, case by case. It covers globals (substituted and renamed), context globals, boxes, `letbox`, the recursors, `CΠ`/`TΠ` and bodied globals. Its syntactic half cites Coq-checked lemmas: `gsubst_gsubst`, `gsubst_subst`, `gsubst_gren_all`, the `ptm`/`pdef` clauses and `gsubstitution`. Its semantic half uses the standard local substitution lemma and a closing lemma for C/D, proved there. It validates `letbox` β, `CΠ`/`TΠ` β/η and the recursors' β. Still open: an independent review of §4.
- 2026-10-13: Decided with the user: doc §1–§6 are frozen after a review that changed no rule. Three wording edits came out of it. (1) §1 now says where the formers live: as `Wf`'s, gated out of layer c until the rec.rs round. (2) §1.1 and §10: `Vec`/`DVec(_; _. T)` and `Wf`/`IWf` at `Unit` are translations, not conversions. At a neutral length they are distinct neutral types, and `elim_Wf`'s ih goes through `nth` where `elim_IWf`'s goes through `dnth`. (3) §3: the ih's type is `F[i]` only up to β, which adds a step to the formalization's hardest `Wf` lemma (`V_nth`); its IWf relation probe checks this first. §10 is decided: option 1 now, option 2 (abbreviations) as the target, after the generator, accepting that it may be slower at first. The no-UIP §4 review is decoupled from the freeze (§12.3, §13 step 1). The stale "Open, before freezing" paragraph is replaced by a status paragraph.
- 2026-10-16: The independent review of `docs/no-uip-model.md` §4 is written: `docs/no-uip-model-review.md`. The outline holds and nothing found touches `UIP₀`, but the interpretation as written misses three rules, each with a local fix: `eqtm_ubeta` when code mentions a bound level (box must evaluate levels), `eqtm_capp` and the other D-conversion congruences (`CΠ`/`TΠ` over conversion classes, with a new representative-independence lemma), and a boxed definition (normalize box values by `unf`). It also lists four missing steps: the recursor's D/V binders, the order of (M1) and the renaming lemma, the lemma's hypotheses, and level binders under `σ` (`guwkn_gosubst`).
- 2026-10-16: The frozen rules are machine-checked in the Coq formalization (heather-coq `M17_DESIGN.md`, main @ 16ed0d5), with no admits or axioms and no change to Heather's rules. M17a: `DVec` at D and M, and `dnth`'s index lemma `V_dnth`, which answers the freeze's one open question: the ih's type being `F[i]` only up to β (doc §3) adds one validity step to `V_nth`'s composition and goes through. The neutral-tuple property is checked on doc §3's own instance (`dnth_reds_example`). M17b: `IWf`, `sup_i`, `elim_IWf` and β on open data at D and M, through the relation (`Wf`'s, with the index an index of the families), the fundamental theorem, decidable conversion, type checking and the consequences. M17c: the codes `TmDVec`/`TmIWf`, the lift to every layer but V, and the six code-recursor branches (`ty_dvec`, `tm_dvec`, `ty_iwf`, `tm_iwf`, `tm_sup_i`, `tm_elim_iwf`; there 55–60), their scopes derived from the layer-C typing rules and validated by `rec_code`. Those scopes are the first precise statement of doc §6, so §13 step 4 (the rec.rs round) checks Heather's branches against them, as M15b did for `Wf`'s, rather than the other way round. `dnth`'s de Bruijn transcription is likewise the statement for step 2's materialization.
- 2026-10-17: The review of `docs/no-uip-model.md` §4 is applied (its new §4.4a maps each finding to its fix). Box values are level-closed and unfolded, environments are `(v, ρ̂)` with V-globals, `CΠ`/`TΠ` range over D-conversion classes with a new representative-independence lemma (M3), the recursors recurse on typed code with `t_λ`'s codomain read up to D-conversion, and the lemma gains its layer-correctness hypothesis, its proof order, (S4u) and the semantic universe substitution lemma. The two pieces the review suggested mechanizing are checked in heather-coq: the `□` fibres' invariance under D-conversion (`Typing/BoxFibre.v`) and `unf`'s idempotence (`unf_idem`, `Syntax/Unfold.v`).
- 2026-10-17: Doc §13 step 2 landed in the kernel: `Type::DVec { level, len, fam }` with `fam` under `i : Fin len`, its two reductions in both reducers (`reduce::step_type`, `Eval::dvec_ty`), neutrality and structural congruence at a neutral length (the family compared under `i : Fin k`), and `term::dnth`, design §3's schema transcribed binder by binder from heather-coq's `tmDNth`. Tests: `crates/kernel/tests/dvec.rs` (11, every verdict asked of both the value machine and the rewriter, every typing of both the gate and `typing::oracle`), plus `DVec` in both term generators and a substitution law for the two new operations, `Type::inst_top` (`t[s/x]` weakened past `k` binders, which the schemas need because they are built without a context) and `shift_local_above`. What the tests pin: the reducts' family instances at `inl ⟨⟩`/`inr j` with `Fin(S k)`'s reduct's annotations, as heather-coq's `red_dvec_succ`; `Vec(T; k)` and `DVec(k; _. T)` converting at a canonical length and not at a neutral one (§1.1); a heterogeneous tuple inhabiting its type, with Σ-η and Unit irrelevance reached through the reduction; `dnth` typing at an open length with a family that mentions its position, so the Unit-η and β steps M17a's `V_dnth` checked are load-bearing here too; and the neutral-tuple property, `dnth(3; F; cs; inr (inl ⟨⟩)) ≡ fst (snd cs)`, by both conversions and by the rewriter's whnf. Two choices: (1) the gate is `Tc::computing_layer`, layers p and m, which is heather-coq's `compt i` and how `Vec` was gated before its codes; since Heather checks declaration bodies at layer c, nothing the elaborator emits can contain a `DVec` until step 4. (2) No `Conv::vec_ty`-style fast path for `DVec`: the design names one only for `Vec` (§10), and nothing hot uses `DVec` yet. Module images and the cache's Merkle hash gain a `DVec` tag (additive, no format bump).
- 2026-10-20: §12.1 and §12.2 checked in the formalization's own rules, ahead of the generator round (§13 step 6): heather-coq `probes/IwfLowering.v`, `M17_DESIGN.md` ("The generator's lowerings"). §8.1's lowering written in the formalization's syntax at layer D for `Vec`, F1–F3 (§8.2), `All p : List a → Type` and `Even`/`Odd` over `Σ(b : Bool). Nat`, each derived with the M17b rules only: typing, β through `elim_IWf` at an open index, and §8.3's form A where it applies, with negative controls (a constructor at a wrong index or tag has no derivation). No family needed a rule the frozen §1–§6 lack. Findings for the generator:
  (1) §8.1's child index "case on the tag, then on the literal position" needs a convoy: the position's type `Fin n[x]` mentions the tag and a case does not refine it, so the tag's case returns `Π(i : Fin n[z]). I` and is applied to `i` (F1). Steps that use the children or the ih at a literal position do the same over `cs` or `ih` (`len`, F1's `left`, F2's `size`, `toNat`). A child index that ignores the position, or a form A arm that reads only the payload, needs none.
  (2) §12.1: form A needs only `I`'s own eliminator, into `Ty 0`: `natrec` at `Nat`, `elim_Wf` at `List a` (tier 0's lowering; nothing more), projections then `Bool`'s case and `natrec` at the Σ index. The arms are codes, so the one extra requirement is on the result: it must have a code (`a`, `⌜Fin k⌝`, `p y`, `⌜Empty⌝`). When the result is a value of the family itself (F1's `left : T (S n) → T 0`), the arm is the family's own code `TmIWf`, so `I` and the shapes need codes too; they have them at `Nat`, and at `List a` (`a` is a code), but inversion to `All p xs` was not checked.
  (3) §12.2: one family over `Σ(tag). I_tag` needs nothing new when the `I_tag` agree: one shape summand per constructor of either family, indices pairing tag and number, mutual recursion as one `elim_IWf` (β across the tags checked), form A at the Σ index with no Σ-η (output indices are literal pairs). A tag-dependent `I_tag` would need the motive's case on `snd j` at a type depending on `fst j`, a convoy again; not checked.
  (4) F2's `n + n` is tier 2, the elaborator's; β at the stuck index is checked.
